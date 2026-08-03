local bridge = peripheral.find("redstone_link_bridge")
assert(bridge, "No redstone_link_bridge found")

--[[====================================================================
  REDSTONE LINK CONTROLLER
  A modern text-based UI for controlling Create "Redstone Link" pairs
  through the PeripheralWorks `redstone_link_bridge` peripheral.

  RESPONSIVENESS ARCHITECTURE
    Input handling, bridge polling, and screen rendering each run as
    independent loops via `parallel.waitForAny`. Input handling never
    performs screen drawing itself (drawing is comparatively slow), so a
    burst of clicks/keys/drags can never back up behind a redraw; a
    dedicated render loop flushes whatever changed to the screen up to
    ~20 times a second, and a separate poll loop talks to the bridge on
    its own schedule. This means a slow bridge or a big redraw can never
    stall input processing.

  VIEWS (press V, or click [V]iew, to switch)
    List view    The scrollable list of saved links/bundles.
    Canvas view  A free-form dashboard of movable, resizable blocks:
                   Text    - a plain label you position anywhere.
                   Input   - read-only display bound to any saved link
                             or bundle member (Toggle or Status).
                   Output  - control bound to a writable link (an
                             Output-mode single link, or a bundle's
                             Toggle). Tapping it toggles 0/15. You can
                             give it a value->text map so instead of
                             "Out: 15" it shows e.g. "Open".

  LIST VIEW CONTROLS
    Arrow Up/Down   Move selection             Mouse click   Select / buttons
    Left / Right    Collapse / expand a bundle  Mouse scroll  Move selection
    PageUp/PageDown Jump a page                 Enter         Full edit
    A               Add new link                D             Delete link/bundle
    R               Rename                      E             Edit frequencies
    Space           Toggle output 0/15*         +             Increase output*
    -               Decrease output*            F             Search / filter
    S               Sort alphabetically         C             Duplicate
    V               Switch to Canvas view       Q             Quit (auto-saves)
    * Space/+/- affect Output-mode links, a bundle's Toggle link, or (if a
      bundle's title row is selected) that bundle's Toggle link directly.

  CANVAS VIEW CONTROLS
    Mouse: drag a block's body to move it. Drag the "#" handle in a
    selected block's bottom-right corner to resize it. A click that ends
    within one character cell of where it started always counts as a
    tap (toggle Output / rebind Input / edit Text), even if the mouse
    drifted slightly - it snaps back rather than silently cancelling.
    Right-click a block to open its editor directly.
    Arrow keys      Move selected block         Shift+Arrows  Resize it
    N               New block                   D             Delete block
    Enter           Edit selected block         Tab           Select next block
    Space           Tap selected block          V             Switch to List view
    Q               Quit (auto-saves)

    NOTE ON KEY REPEATS: Minecraft resends "key" events continuously while
    a key stays physically held down. Discrete actions ignore those
    repeat events and only fire once per physical press - otherwise a
    press held a fraction of a second too long could double-fire (e.g.
    toggle a value twice) and appear to do nothing.

  Only bridge.getLinkSignal(freq1, freq2) and bridge.sendLinkSignal
  (freq1, freq2, strength) are ever called on the peripheral, as required.
======================================================================]]

-- ======================================================================
-- CONFIGURATION
-- ======================================================================
local SAVE_FILE             = "redstone_links.dat"
local POLL_TICK              = 0.2    -- seconds between bridge polls (several/sec)
local RENDER_TICK            = 0.05   -- seconds between screen flushes (~20 fps cap)
local BG_POLL_PER_TICK       = 6      -- off-screen links refreshed per poll tick
local CHAR_DEBOUNCE_INTERVAL = 0.15   -- min seconds between +/- char triggers
local HEADER_HEIGHT          = 2
local FOOTER_HEIGHT          = 3

local W, H = term.getSize()
local LIST_TOP    = HEADER_HEIGHT + 1
local LIST_BOTTOM = H - FOOTER_HEIGHT
local LIST_HEIGHT = math.max(1, LIST_BOTTOM - LIST_TOP + 1)

-- ======================================================================
-- CONSTANTS: link entry kinds and link modes
-- ======================================================================
local KIND_SINGLE = "single"  -- a standalone link
local KIND_BUNDLE = "bundle"  -- a Toggle + Status pair grouped together

local MODE_OUTPUT = "output"  -- can be sent to / toggled
local MODE_INPUT  = "input"   -- read-only, shows received signal

-- ======================================================================
-- CONSTANTS: canvas view block types and sizing rules
-- ======================================================================
local BLOCK_TEXT   = "text"
local BLOCK_INPUT  = "input"
local BLOCK_OUTPUT = "output"

local MIN_TEXT_W, MIN_TEXT_H         = 3, 1
local MIN_WIDGET_W, MIN_WIDGET_H     = 8, 2
local DEFAULT_TEXT_W, DEFAULT_TEXT_H = 12, 1
local DEFAULT_WIDGET_W, DEFAULT_WIDGET_H = 14, 3

-- ======================================================================
-- BRIDGE CONNECTION STATE
-- ======================================================================
local bridgeConn = {
  peripheral = bridge,
  connected  = true,
}

-- ======================================================================
-- APPLICATION STATE
-- ======================================================================
local links = {}
--[[
  Single entry:
    { id=N, kind=KIND_SINGLE, name=, mode=MODE_OUTPUT/MODE_INPUT,
      freq1=, freq2=, output=0, input=0 }
  Bundle entry:
    { id=N, kind=KIND_BUNDLE, name=, expanded=true/false,
      toggle = { mode=MODE_OUTPUT, freq1=, freq2=, output=0, input=0 },
      status = { mode=MODE_INPUT,  freq1=, freq2=, output=0, input=0 } }

  `id` is a stable identifier that never changes and is never reused,
  even if the entry is later moved, sorted, or other entries around it
  are deleted. Canvas blocks reference links by this id (not by their
  position in the array) so bindings never silently point at the wrong
  link after the list is edited, deleted from, or reordered.
]]
local nextLinkId = 1

local displayRows      = {}  -- flattened, filtered rows currently shown (list view)
                              -- { rowType="single"/"bundleHeader"/
                              --   "bundleToggle"/"bundleStatus", linkIndex=N }
local matchedEntryCount = 0  -- number of top-level entries matching the filter
local filterText        = ""
local sortAscending      = true
local selected           = 0   -- index into displayRows (0 = none)
local scrollOffset       = 0

local appMode           = "list"  -- "list" or "canvas"
local canvasBlocks      = {}      -- { {type=,x=,y=,w=,h=,text=,label=,
                                   --    linkId=,memberKey=,labels={}}, ... }
local selectedBlockIndex = 0
local dragState           = nil    -- {mode="move"/"resize", blockIndex=, ...}
local isShiftDown         = false

local statusMsg          = ""
local statusColor        = colors.lightGray
local statusExpireAt     = 0
local footerButtons      = {}  -- clickable regions: {x1,x2,y,action}
local rowClickZones      = {}  -- clickable sub-regions on list rows
local charDebounce       = { ["+"] = 0, ["-"] = 0 } -- last-fired time for char keys
local dirty              = { header = true, body = true, footer = true }
local running            = true
local dataDirty          = false
local bgPollIndex        = 1

-- True while a modal dialog (readLineInput/promptX/choiceDialog/etc.) is
-- on screen. The render loop checks this and skips redrawing so it can
-- never paint over a dialog box; dialogs draw their own contents.
local suspendRender      = false

-- ======================================================================
-- FORWARD DECLARATIONS
-- (declared here so functions may reference each other regardless of
-- the order they are ultimately defined further down this file)
-- ======================================================================
local checkBridgeConnection, tryFindBridge, safeGetSignal, safeSendSignal
local saveData, loadData
local refreshDisplayRows, ensureVisible, getSelectedRow, selectEntryByLinkIndex
local writeLine, drawBox, drawButtonRow
local drawSingleRow, drawBundleHeaderRow, drawBundleMemberRow
local drawHeader, drawList, drawFooter, drawCanvas, drawBlock
local markDirty, redraw, refreshAfterDialog, setStatus
local readLineInput, choiceDialog, promptSingleField, promptTwoFields
local promptEntryKind, promptLinkMode, promptNameAndFreqs
local singleLinkFullEditFlow, bundleFullEditFlow, confirmDialog
local pickLinkDialog, labelsEditorDialog
local applyOutput, getTogglablePollable, toggleBundleExpanded
local findLinkEntryById, resolveBlockSource, getBlockDisplayName, buildCandidates, findBlockAt
local actionAdd, actionDelete, actionRename, actionEditFrequencies
local actionEditFull, actionDuplicate
local actionToggleOutput, actionIncOutput, actionDecOutput
local actionFilter, sortLinksAlpha
local actionAddBlock, actionEditBlock, actionDeleteBlock, actionTapBlock
local selectNextBlock, clampAllBlocksToScreen
local handleKey, handleChar, handleMouseClick, handleMouseScroll
local handleCanvasKey, handleCanvasMouseClick, handleCanvasMouseDrag
local handleCanvasMouseUp, handleCanvasMouseScroll
local handleGlobalKey, toggleViewMode, actionQuit
local collectPriorityEntries, pollVisible, pollBackground
local inputLoop, pollLoop, renderLoop, main

-- ======================================================================
-- SMALL UTILITIES
-- ======================================================================
local function trim(s)
  return (s or ""):match("^%s*(.-)%s*$")
end

local function clamp(v, lo, hi)
  if v < lo then return lo end
  if v > hi then return hi end
  return v
end

-- ======================================================================
-- BRIDGE COMMUNICATION (only getLinkSignal / sendLinkSignal are used
-- for the Redstone Link itself; peripheral.find/getName/isPresent are
-- ordinary peripheral-discovery calls used only to detect connectivity)
-- ======================================================================
tryFindBridge = function()
  local wasDisconnected = not bridgeConn.connected
  local p = peripheral.find("redstone_link_bridge")
  if p then
    bridgeConn.peripheral = p
    bridgeConn.connected = true
    if wasDisconnected then
      -- Bridge came back: push every stored OUTPUT value back out so the
      -- physical redstone state matches what the UI shows.
      for _, entry in ipairs(links) do
        if entry.kind == KIND_SINGLE then
          if entry.mode == MODE_OUTPUT then
            pcall(p.sendLinkSignal, entry.freq1, entry.freq2, entry.output or 0)
          end
        else
          pcall(p.sendLinkSignal, entry.toggle.freq1, entry.toggle.freq2, entry.toggle.output or 0)
        end
      end
      setStatus("Bridge reconnected - outputs restored.", colors.lime)
    end
  else
    bridgeConn.connected = false
  end
  return bridgeConn.connected
end

-- Runs every poll tick regardless of which link modes exist, so a
-- disconnect/reconnect is always detected promptly even if every saved
-- link happens to be output-only (and therefore never calls getLinkSignal).
checkBridgeConnection = function()
  if bridgeConn.connected then
    local ok, name = pcall(peripheral.getName, bridgeConn.peripheral)
    if not ok or not name or not peripheral.isPresent(name) then
      bridgeConn.connected = false
    end
  else
    tryFindBridge()
  end
end

safeGetSignal = function(f1, f2)
  if not bridgeConn.connected and not tryFindBridge() then
    return nil
  end
  local ok, result = pcall(bridgeConn.peripheral.getLinkSignal, f1, f2)
  if ok then return result end
  bridgeConn.connected = false
  return nil
end

safeSendSignal = function(f1, f2, strength)
  if not bridgeConn.connected and not tryFindBridge() then
    return false
  end
  local ok = pcall(bridgeConn.peripheral.sendLinkSignal, f1, f2, strength)
  if not ok then
    bridgeConn.connected = false
    return false
  end
  return true
end

-- ======================================================================
-- STABLE LINK LOOKUP (used by canvas blocks; see `id` note above)
-- ======================================================================
findLinkEntryById = function(id)
  if not id then return nil end
  for _, entry in ipairs(links) do
    if entry.id == id then return entry end
  end
  return nil
end

-- ======================================================================
-- PERSISTENCE
-- ======================================================================
saveData = function()
  local linkData = {}
  for i, entry in ipairs(links) do
    if entry.kind == KIND_BUNDLE then
      linkData[i] = {
        id   = entry.id,
        kind = KIND_BUNDLE,
        name = entry.name,
        toggleFreq1  = entry.toggle.freq1,
        toggleFreq2  = entry.toggle.freq2,
        toggleOutput = entry.toggle.output or 0,
        statusFreq1  = entry.status.freq1,
        statusFreq2  = entry.status.freq2,
      }
    else
      linkData[i] = {
        id     = entry.id,
        kind   = KIND_SINGLE,
        name   = entry.name,
        mode   = entry.mode,
        freq1  = entry.freq1,
        freq2  = entry.freq2,
        output = entry.output or 0,
      }
    end
  end

  local blockData = {}
  for i, block in ipairs(canvasBlocks) do
    blockData[i] = {
      type = block.type, x = block.x, y = block.y, w = block.w, h = block.h,
      text = block.text, label = block.label,
      linkId = block.linkId, memberKey = block.memberKey,
      labels = block.labels,
    }
  end

  local payload = { links = linkData, blocks = blockData, viewMode = appMode }
  local ok, serialized = pcall(textutils.serialize, payload)
  if not ok then
    setStatus("Error serializing save data!", colors.red)
    return false
  end
  local file, err = fs.open(SAVE_FILE, "w")
  if not file then
    setStatus("Error saving file: " .. tostring(err), colors.red)
    return false
  end
  file.write(serialized)
  file.close()
  return true
end

loadData = function()
  if not fs.exists(SAVE_FILE) then
    -- Create the save file if it does not exist yet.
    local file = fs.open(SAVE_FILE, "w")
    if file then
      file.write(textutils.serialize({ links = {}, blocks = {}, viewMode = "list" }))
      file.close()
    end
    links = {}
    canvasBlocks = {}
    return
  end

  local file = fs.open(SAVE_FILE, "r")
  if not file then
    links = {}
    canvasBlocks = {}
    return
  end
  local content = file.readAll()
  file.close()

  local ok, data = pcall(textutils.unserialize, content)
  links = {}
  canvasBlocks = {}

  local rawLinks, rawBlocks = {}, {}
  if ok and type(data) == "table" then
    if data.links ~= nil or data.blocks ~= nil then
      rawLinks = data.links or {}
      rawBlocks = data.blocks or {}
      if data.viewMode == "canvas" then appMode = "canvas" end
    else
      rawLinks = data -- legacy save file: a plain array of link items
    end
  end

  -- Parse links, assigning a stable id to any entry that doesn't already
  -- have one (legacy files saved before ids existed).
  for _, item in ipairs(rawLinks) do
    if type(item) == "table" and item.name ~= nil then
      local id = tonumber(item.id)
      if not id then
        id = nextLinkId
        nextLinkId = nextLinkId + 1
      else
        nextLinkId = math.max(nextLinkId, id + 1)
      end

      if item.kind == KIND_BUNDLE and item.toggleFreq1 ~= nil and item.toggleFreq2 ~= nil
         and item.statusFreq1 ~= nil and item.statusFreq2 ~= nil then
        links[#links + 1] = {
          id = id,
          kind = KIND_BUNDLE,
          name = tostring(item.name),
          expanded = true, -- fold state is transient UI state, always start expanded
          toggle = {
            mode = MODE_OUTPUT, freq1 = item.toggleFreq1, freq2 = item.toggleFreq2,
            output = tonumber(item.toggleOutput) or 0, input = 0,
          },
          status = {
            mode = MODE_INPUT, freq1 = item.statusFreq1, freq2 = item.statusFreq2,
            output = 0, input = 0,
          },
        }
      elseif item.freq1 ~= nil and item.freq2 ~= nil then
        -- KIND_SINGLE, or a legacy entry saved before link modes existed
        -- (no "mode" field) - default those to Output to preserve old behavior.
        local mode = item.mode
        if mode ~= MODE_INPUT and mode ~= MODE_OUTPUT then mode = MODE_OUTPUT end
        links[#links + 1] = {
          id = id,
          kind = KIND_SINGLE,
          name = tostring(item.name),
          mode = mode,
          freq1 = item.freq1,
          freq2 = item.freq2,
          output = tonumber(item.output) or 0,
          input = 0,
        }
      end
    end
  end

  -- Parse canvas blocks, validating & defaulting any missing/invalid fields
  -- so a corrupted or hand-edited save file can never crash the program.
  for _, item in ipairs(rawBlocks) do
    if type(item) == "table" and (item.type == BLOCK_TEXT or item.type == BLOCK_INPUT or item.type == BLOCK_OUTPUT) then
      local block = {
        type = item.type,
        x = tonumber(item.x) or 2,
        y = tonumber(item.y) or LIST_TOP,
        w = math.max(1, tonumber(item.w) or DEFAULT_WIDGET_W),
        h = math.max(1, tonumber(item.h) or DEFAULT_WIDGET_H),
        text = tostring(item.text or ""),
        label = tostring(item.label or ""),
        linkId = tonumber(item.linkId),
        memberKey = (item.memberKey == "toggle" or item.memberKey == "status") and item.memberKey or nil,
        labels = {},
      }
      if type(item.labels) == "table" then
        for k, v in pairs(item.labels) do
          local nk = tonumber(k)
          if nk and v ~= nil then block.labels[nk] = tostring(v) end
        end
      end

      local minW = (block.type == BLOCK_TEXT) and MIN_TEXT_W or MIN_WIDGET_W
      local minH = (block.type == BLOCK_TEXT) and MIN_TEXT_H or MIN_WIDGET_H
      block.w = clamp(block.w, minW, W)
      block.h = clamp(block.h, minH, math.max(minH, LIST_BOTTOM - LIST_TOP + 1))
      block.x = clamp(block.x, 1, math.max(1, W - block.w + 1))
      block.y = clamp(block.y, LIST_TOP, math.max(LIST_TOP, LIST_BOTTOM - block.h + 1))
      canvasBlocks[#canvasBlocks + 1] = block
    end
  end
end

-- ======================================================================
-- FILTER / SORT / SELECTION NAVIGATION (list view)
-- ======================================================================
refreshDisplayRows = function()
  displayRows = {}
  matchedEntryCount = 0
  local ft = filterText:lower()
  for i, entry in ipairs(links) do
    if ft == "" or entry.name:lower():find(ft, 1, true) then
      matchedEntryCount = matchedEntryCount + 1
      if entry.kind == KIND_SINGLE then
        displayRows[#displayRows + 1] = { rowType = "single", linkIndex = i }
      else
        displayRows[#displayRows + 1] = { rowType = "bundleHeader", linkIndex = i }
        if entry.expanded ~= false then
          displayRows[#displayRows + 1] = { rowType = "bundleToggle", linkIndex = i }
          displayRows[#displayRows + 1] = { rowType = "bundleStatus", linkIndex = i }
        end
      end
    end
  end
  if #displayRows == 0 then
    selected = 0
  elseif selected < 1 or selected > #displayRows then
    selected = 1
  end
  ensureVisible()
  markDirty("body")
  markDirty("header")
end

ensureVisible = function()
  if selected < 1 then
    scrollOffset = 0
    return
  end
  if selected <= scrollOffset then
    scrollOffset = selected - 1
  elseif selected > scrollOffset + LIST_HEIGHT then
    scrollOffset = selected - LIST_HEIGHT
  end
  local maxScroll = math.max(0, #displayRows - LIST_HEIGHT)
  scrollOffset = clamp(scrollOffset, 0, maxScroll)
end

getSelectedRow = function()
  if selected < 1 or selected > #displayRows then return nil end
  return displayRows[selected]
end

selectEntryByLinkIndex = function(idx)
  for i, row in ipairs(displayRows) do
    if row.linkIndex == idx and (row.rowType == "single" or row.rowType == "bundleHeader") then
      selected = i
      ensureVisible()
      return
    end
  end
end

sortLinksAlpha = function()
  sortAscending = not sortAscending
  table.sort(links, function(a, b)
    local na, nb = a.name:lower(), b.name:lower()
    if sortAscending then return na < nb else return na > nb end
  end)
  dataDirty = true
  refreshDisplayRows()
  setStatus("Sorted " .. (sortAscending and "A-Z" or "Z-A") .. ".", colors.lightBlue)
end

-- Flips a bundle's collapsed/expanded state and keeps the selection on
-- that bundle's title row afterward (its sub-rows may have just vanished).
toggleBundleExpanded = function(linkIndex)
  local entry = links[linkIndex]
  if not entry or entry.kind ~= KIND_BUNDLE then return end
  local currentlyExpanded = entry.expanded ~= false
  entry.expanded = not currentlyExpanded
  refreshDisplayRows()
  selectEntryByLinkIndex(linkIndex)
  markDirty("body")
end

-- ======================================================================
-- LOW-LEVEL DRAWING HELPERS (flicker-free: always overwrite full width)
-- ======================================================================
writeLine = function(y, text, fg, bg)
  term.setCursorPos(1, y)
  term.setBackgroundColor(bg or colors.black)
  term.setTextColor(fg or colors.white)
  local s = text or ""
  if #s > W then s = s:sub(1, W) end
  term.write(s .. string.rep(" ", W - #s))
end

drawBox = function(x, y, width, height, title)
  for row = 0, height - 1 do
    term.setCursorPos(x, y + row)
    term.setBackgroundColor(colors.gray)
    term.setTextColor(colors.white)
    term.write(string.rep(" ", width))
  end
  term.setCursorPos(x + 1, y)
  term.setBackgroundColor(colors.lightBlue)
  term.setTextColor(colors.black)
  local t = title or ""
  if #t > width - 2 then t = t:sub(1, width - 2) end
  term.write(t)
end

drawButtonRow = function(y, specs)
  term.setCursorPos(1, y)
  term.setBackgroundColor(colors.gray)
  term.setTextColor(colors.white)
  term.write(string.rep(" ", W))
  local x = 1
  for _, spec in ipairs(specs) do
    local label = spec.label
    if x + #label <= W + 1 then
      term.setCursorPos(x, y)
      local closeBracket = label:find("%]")
      if closeBracket then
        term.setTextColor(colors.yellow)
        term.write(label:sub(1, closeBracket))
        term.setTextColor(colors.white)
        term.write(label:sub(closeBracket + 1))
      else
        term.setTextColor(colors.white)
        term.write(label)
      end
      if spec.action then
        footerButtons[#footerButtons + 1] =
          { x1 = x, x2 = x + #label - 1, y = y, action = spec.action }
      end
      x = x + #label + 1
    end
  end
end

local function shortText(value, maxLen)
  local s = tostring(value)
  if #s > maxLen then s = s:sub(1, maxLen - 1) .. "~" end
  return s
end

-- A standalone single link row: name + F1/F2 + only the relevant of In/Out.
drawSingleRow = function(y, entry, isSelected)
  term.setBackgroundColor(isSelected and colors.gray or colors.black)

  local isOut = entry.mode == MODE_OUTPUT
  local roleTag = isOut and "OUT" or "IN "
  local freq1s = shortText(entry.freq1, 7)
  local freq2s = shortText(entry.freq2, 7)
  local inS  = isOut and " --" or string.format("%3d", entry.input or 0)
  local outS = isOut and string.format("%3d", entry.output or 0) or " --"

  local marker = isSelected and "> " or "  "
  local usedSoFar = #marker + #roleTag + 1
  local suffix = string.format(" F1:%-7s F2:%-7s In:%s Out:%s ", freq1s, freq2s, inS, outS)
  local nameWidth = math.max(3, W - usedSoFar - #suffix)

  local name = entry.name or ""
  if #name > nameWidth then name = name:sub(1, math.max(1, nameWidth - 1)) .. "~" end
  name = name .. string.rep(" ", nameWidth - #name)

  term.setCursorPos(1, y)
  term.setTextColor(isSelected and colors.white or colors.lightGray)
  term.write(marker)
  term.setTextColor(isOut and colors.orange or colors.lightBlue)
  term.write(roleTag)
  term.setTextColor(colors.white)
  term.write(" ")
  term.setTextColor(isSelected and colors.yellow or colors.white)
  term.write(name)

  term.setTextColor(colors.lightGray); term.write(" F1:")
  term.setTextColor(colors.lightBlue); term.write(string.format("%-7s", freq1s))
  term.setTextColor(colors.lightGray); term.write(" F2:")
  term.setTextColor(colors.lightBlue); term.write(string.format("%-7s", freq2s))
  term.setTextColor(colors.lightGray); term.write(" In:")
  term.setTextColor(isOut and colors.gray or ((entry.input or 0) > 0 and colors.lime or colors.gray))
  term.write(inS)
  term.setTextColor(colors.lightGray); term.write(" Out:")
  term.setTextColor((not isOut) and colors.gray or ((entry.output or 0) > 0 and colors.orange or colors.gray))
  term.write(outS)
  term.setTextColor(colors.white); term.write(" ")

  local cx = select(1, term.getCursorPos())
  if cx <= W then term.write(string.rep(" ", W - cx + 1)) end
end

-- A bundle's title/header row: [-]/[+] fold indicator (clickable), name,
-- and a live Tgl/Sta summary where the "Tgl:xxx" text is also clickable.
-- Both clickable zones are recorded into rowClickZones for the mouse
-- handler to use; drawList() resets that table once per full redraw.
drawBundleHeaderRow = function(y, entry, linkIndex, isSelected)
  term.setBackgroundColor(isSelected and colors.gray or colors.black)
  term.setCursorPos(1, y)

  local marker = isSelected and "> " or "  "
  term.setTextColor(isSelected and colors.white or colors.lightGray)
  term.write(marker)

  -- Fold indicator: click to expand/collapse this bundle.
  local expanded = entry.expanded ~= false
  local expandX1 = select(1, term.getCursorPos())
  term.setTextColor(colors.yellow)
  term.write(expanded and "[-]" or "[+]")
  local expandX2 = select(1, term.getCursorPos()) - 1
  rowClickZones[#rowClickZones + 1] =
    { x1 = expandX1, x2 = expandX2, y = y, kind = "expand", linkIndex = linkIndex }

  term.setTextColor(colors.white); term.write(" ")
  term.setTextColor(colors.pink);  term.write("GROUP ")

  local toggleOn = (entry.toggle.output or 0) > 0
  local toggleTxt = toggleOn and "ON " or "OFF"
  local statusVal = entry.status.input or 0
  local tailWidth = #(" Tgl:" .. toggleTxt) + #(string.format("  Sta:%2d ", statusVal))
  local usedSoFar = select(1, term.getCursorPos()) - 1
  local nameWidth = math.max(3, W - usedSoFar - tailWidth)

  local name = entry.name or ""
  if #name > nameWidth then name = name:sub(1, math.max(1, nameWidth - 1)) .. "~" end
  name = name .. string.rep(" ", nameWidth - #name)
  term.setTextColor(isSelected and colors.yellow or colors.white)
  term.write(name)

  term.setTextColor(colors.lightGray); term.write(" Tgl:")
  -- Toggle summary text: click to toggle this bundle's output directly.
  local toggleX1 = select(1, term.getCursorPos())
  term.setTextColor(toggleOn and colors.orange or colors.gray)
  term.write(toggleTxt)
  local toggleX2 = select(1, term.getCursorPos()) - 1
  rowClickZones[#rowClickZones + 1] =
    { x1 = toggleX1, x2 = toggleX2, y = y, kind = "toggleGroup", linkIndex = linkIndex }

  term.setTextColor(colors.lightGray); term.write("  Sta:")
  term.setTextColor(statusVal > 0 and colors.lime or colors.gray)
  term.write(string.format("%2d", statusVal))
  term.setTextColor(colors.white); term.write(" ")

  local cx = select(1, term.getCursorPos())
  if cx <= W then term.write(string.rep(" ", W - cx + 1)) end
end

-- A bundle's Toggle or Status sub-row: indented, shows its own F1/F2/value.
drawBundleMemberRow = function(y, label, member, isSelected, isOutputRole)
  term.setBackgroundColor(isSelected and colors.gray or colors.black)

  local marker = isSelected and "  > " or "    "
  local freq1s = shortText(member.freq1, 8)
  local freq2s = shortText(member.freq2, 8)
  local valLabel = isOutputRole and "Out" or "In "
  local val = isOutputRole and (member.output or 0) or (member.input or 0)

  term.setCursorPos(1, y)
  term.setTextColor(isSelected and colors.white or colors.lightGray)
  term.write(marker)
  term.setTextColor(isOutputRole and colors.orange or colors.lightBlue)
  term.write(string.format("%-8s", label))
  term.setTextColor(colors.lightGray); term.write("F1:")
  term.setTextColor(colors.lightBlue); term.write(string.format("%-8s", freq1s))
  term.setTextColor(colors.lightGray); term.write("F2:")
  term.setTextColor(colors.lightBlue); term.write(string.format("%-8s", freq2s))
  term.setTextColor(colors.lightGray); term.write(valLabel .. ":")
  term.setTextColor(val > 0 and (isOutputRole and colors.orange or colors.lime) or colors.gray)
  term.write(string.format("%2d", val))
  term.setTextColor(colors.white); term.write(" ")

  local cx = select(1, term.getCursorPos())
  if cx <= W then term.write(string.rep(" ", W - cx + 1)) end
end

-- ======================================================================
-- CANVAS VIEW: block resolution and rendering
-- ======================================================================

-- Resolves a canvas block to the underlying pollable table (which has
-- freq1/freq2/input/output fields) and whether it can be written to.
-- Returns nil, false if the block isn't bound or its link was deleted.
resolveBlockSource = function(block)
  local entry = findLinkEntryById(block.linkId)
  if not entry then return nil, false end
  if entry.kind == KIND_SINGLE then
    if block.memberKey then return nil, false end
    return entry, (entry.mode == MODE_OUTPUT)
  else
    if block.memberKey == "toggle" then return entry.toggle, true
    elseif block.memberKey == "status" then return entry.status, false
    else return nil, false end
  end
end

getBlockDisplayName = function(block)
  if block.label and block.label ~= "" then return block.label end
  local entry = findLinkEntryById(block.linkId)
  if not entry then return "(unbound)" end
  if block.memberKey == "toggle" then return entry.name .. " (Toggle)"
  elseif block.memberKey == "status" then return entry.name .. " (Status)"
  else return entry.name end
end

-- Builds the list of {label=, linkId=, memberKey=} candidates a block of
-- the given type can bind to. Output blocks only offer writable sources;
-- Input blocks (pure display) offer everything, tagged with its role.
buildCandidates = function(blockType)
  local candidates = {}
  for _, entry in ipairs(links) do
    if entry.kind == KIND_SINGLE then
      if blockType == BLOCK_OUTPUT then
        if entry.mode == MODE_OUTPUT then
          candidates[#candidates + 1] = { label = entry.name .. " [Output]", linkId = entry.id, memberKey = nil }
        end
      else
        local tag = (entry.mode == MODE_OUTPUT) and "[Output]" or "[Input]"
        candidates[#candidates + 1] = { label = entry.name .. " " .. tag, linkId = entry.id, memberKey = nil }
      end
    else
      if blockType == BLOCK_OUTPUT then
        candidates[#candidates + 1] = { label = entry.name .. " - Toggle [Output]", linkId = entry.id, memberKey = "toggle" }
      else
        candidates[#candidates + 1] = { label = entry.name .. " - Toggle [Output]", linkId = entry.id, memberKey = "toggle" }
        candidates[#candidates + 1] = { label = entry.name .. " - Status [Input]", linkId = entry.id, memberKey = "status" }
      end
    end
  end
  return candidates
end

-- Topmost block (highest index = drawn last = on top) whose rectangle
-- contains the given screen coordinate, or nil if none.
findBlockAt = function(x, y)
  for i = #canvasBlocks, 1, -1 do
    local b = canvasBlocks[i]
    if x >= b.x and x <= b.x + b.w - 1 and y >= b.y and y <= b.y + b.h - 1 then
      return i
    end
  end
  return nil
end

-- Greedy word-wrap of `text` into at most `maxLines` lines of `width`
-- characters, hard-breaking any single word longer than the width.
local function wrapText(text, width, maxLines)
  local words = {}
  for w_ in (text or ""):gmatch("%S+") do words[#words + 1] = w_ end

  local lines = {}
  local cur = ""
  for _, w_ in ipairs(words) do
    if #lines >= maxLines then break end
    local candidate = (cur == "") and w_ or (cur .. " " .. w_)
    if #candidate <= width then
      cur = candidate
    else
      if cur ~= "" then lines[#lines + 1] = cur; cur = "" end
      if #lines >= maxLines then break end
      if #w_ > width then
        local remaining = w_
        while #remaining > width and #lines < maxLines do
          lines[#lines + 1] = remaining:sub(1, width)
          remaining = remaining:sub(width + 1)
        end
        cur = remaining
      else
        cur = w_
      end
    end
  end
  if #lines < maxLines and cur ~= "" then lines[#lines + 1] = cur end
  if #lines == 0 then lines[1] = "" end
  return lines
end

drawBlock = function(block, isSelected)
  local x1 = clamp(block.x, 1, W)
  local y1 = clamp(block.y, LIST_TOP, LIST_BOTTOM)
  local x2 = clamp(block.x + block.w - 1, 1, W)
  local y2 = clamp(block.y + block.h - 1, LIST_TOP, LIST_BOTTOM)
  if x2 < x1 or y2 < y1 then return end -- fully off-screen, nothing to draw

  local bg, fg
  if block.type == BLOCK_TEXT then
    bg = isSelected and colors.lightGray or colors.gray
    fg = colors.black
  elseif block.type == BLOCK_INPUT then
    bg = isSelected and colors.lightBlue or colors.blue
    fg = colors.white
  else
    bg = isSelected and colors.orange or colors.brown
    fg = colors.white
  end

  for y = y1, y2 do
    term.setCursorPos(x1, y)
    term.setBackgroundColor(bg)
    term.write(string.rep(" ", x2 - x1 + 1))
  end
  local w = x2 - x1 + 1

  if block.type == BLOCK_TEXT then
    local lines = wrapText(block.text, w, y2 - y1 + 1)
    for i, line in ipairs(lines) do
      term.setCursorPos(x1, y1 + i - 1)
      term.setBackgroundColor(bg); term.setTextColor(fg)
      term.write(line)
    end
  else
    term.setCursorPos(x1, y1)
    term.setBackgroundColor(bg); term.setTextColor(fg)
    local name = getBlockDisplayName(block)
    if #name > w then name = name:sub(1, math.max(1, w - 1)) .. "~" end
    term.write(name)

    if y2 >= y1 + 1 then
      term.setCursorPos(x1, y1 + 1)
      term.setBackgroundColor(bg)
      local pollable, canWrite = resolveBlockSource(block)
      local valueText
      if not pollable then
        term.setTextColor(colors.red)
        valueText = "(unbound)"
      else
        local raw = canWrite and (pollable.output or 0) or (pollable.input or 0)
        local labelStr = block.labels and block.labels[raw]
        valueText = labelStr or ((canWrite and "Out: " or "In: ") .. tostring(raw))
        term.setTextColor(raw > 0 and colors.yellow or fg)
      end
      if #valueText > w then valueText = valueText:sub(1, math.max(1, w - 1)) .. "~" end
      term.write(valueText .. string.rep(" ", math.max(0, w - #valueText)))
    end

    if y2 >= y1 + 2 then
      term.setCursorPos(x1, y1 + 2)
      term.setBackgroundColor(bg); term.setTextColor(colors.lightGray)
      local pollable2 = resolveBlockSource(block)
      local freqText = pollable2 and ("F1:" .. tostring(pollable2.freq1) .. " F2:" .. tostring(pollable2.freq2)) or ""
      if #freqText > w then freqText = freqText:sub(1, math.max(1, w - 1)) .. "~" end
      term.write(freqText .. string.rep(" ", math.max(0, w - #freqText)))
    end
  end

  -- Resize handle: only shown on the selected block, bottom-right corner.
  if isSelected then
    term.setCursorPos(x2, y2)
    term.setBackgroundColor(colors.yellow)
    term.setTextColor(colors.black)
    term.write("#")
  end
end

drawCanvas = function()
  for y = LIST_TOP, LIST_BOTTOM do
    writeLine(y, "", colors.white, colors.black)
  end
  for idx, block in ipairs(canvasBlocks) do
    drawBlock(block, idx == selectedBlockIndex)
  end
  if #canvasBlocks == 0 then
    local msg = "No blocks yet. Press [N] or click [N]ew to add one."
    local y = math.floor((LIST_TOP + LIST_BOTTOM) / 2)
    local x = math.max(1, math.floor((W - #msg) / 2) + 1)
    term.setCursorPos(x, y)
    term.setBackgroundColor(colors.black)
    term.setTextColor(colors.gray)
    term.write(msg)
  end
end

-- ======================================================================
-- MAIN UI SECTIONS
-- ======================================================================
drawHeader = function()
  term.setCursorPos(1, 1)
  term.setBackgroundColor(colors.blue)
  term.setTextColor(colors.white)
  local title = " Redstone Link Controller"
  local status = bridgeConn.connected and "ONLINE" or "OFFLINE"
  local statusText = " BRIDGE: " .. status .. " "
  local gap = math.max(0, W - #title - #statusText)
  term.write(title .. string.rep(" ", gap))
  term.setBackgroundColor(colors.blue)
  term.setTextColor(bridgeConn.connected and colors.lime or colors.red)
  term.write(statusText)

  local info
  if appMode == "list" then
    local filterDisp = (filterText ~= "") and filterText or "(none)"
    info = string.format(" Search: %s | Sort: %s | Links: %d/%d",
      filterDisp, sortAscending and "A-Z" or "Z-A", matchedEntryCount, #links)
  else
    local selName = "(none)"
    if selectedBlockIndex > 0 and canvasBlocks[selectedBlockIndex] then
      selName = getBlockDisplayName(canvasBlocks[selectedBlockIndex])
    end
    info = string.format(" View: Canvas | Blocks: %d | Selected: %s", #canvasBlocks, selName)
  end
  writeLine(2, info, colors.lightGray, colors.gray)
end

drawList = function()
  rowClickZones = {}

  local count = #displayRows
  if count == 0 then
    local msg
    if #links == 0 then
      msg = "No links yet. Press [A] or click [A]dd to create one."
    else
      msg = "No links match filter '" .. filterText .. "'."
    end
    writeLine(LIST_TOP, msg, colors.gray, colors.black)
    for row = LIST_TOP + 1, LIST_BOTTOM do
      writeLine(row, "", colors.white, colors.black)
    end
    return
  end

  for row = 0, LIST_HEIGHT - 1 do
    local y = LIST_TOP + row
    local ri = scrollOffset + row + 1
    local drow = displayRows[ri]
    if drow then
      local entry = links[drow.linkIndex]
      local isSelected = (ri == selected)
      if drow.rowType == "single" then
        drawSingleRow(y, entry, isSelected)
      elseif drow.rowType == "bundleHeader" then
        drawBundleHeaderRow(y, entry, drow.linkIndex, isSelected)
      elseif drow.rowType == "bundleToggle" then
        drawBundleMemberRow(y, "Toggle", entry.toggle, isSelected, true)
      elseif drow.rowType == "bundleStatus" then
        drawBundleMemberRow(y, "Status", entry.status, isSelected, false)
      end
    else
      writeLine(y, "", colors.white, colors.black)
    end
  end
end

drawFooter = function()
  footerButtons = {}

  local msg, col
  if statusMsg ~= "" then
    msg, col = statusMsg, statusColor
  elseif not bridgeConn.connected then
    msg, col = "Bridge disconnected - attempting to reconnect...", colors.red
  else
    msg, col = "Ready.", colors.lightGray
  end
  writeLine(H - 2, msg, col, colors.black)

  if appMode == "list" then
    drawButtonRow(H - 1, {
      { label = "[A]dd",       action = actionAdd },
      { label = "[D]el",       action = actionDelete },
      { label = "[R]en",       action = actionRename },
      { label = "[E]Frq",      action = actionEditFrequencies },
      { label = "[C]opy",      action = actionDuplicate },
      { label = "[Ent]Edit",   action = actionEditFull },
      { label = "[F]ind",      action = actionFilter },
    })
    drawButtonRow(H, {
      { label = "[Spc]Tgl",    action = actionToggleOutput },
      { label = "[+]Inc",      action = actionIncOutput },
      { label = "[-]Dec",      action = actionDecOutput },
      { label = "[S]ort",      action = sortLinksAlpha },
      { label = "[V]iew",      action = toggleViewMode },
      { label = "[Q]uit",      action = actionQuit },
    })
  else
    drawButtonRow(H - 1, {
      { label = "[N]ew",       action = actionAddBlock },
      { label = "[D]el",       action = actionDeleteBlock },
      { label = "[Ent]Edit",   action = function() actionEditBlock(selectedBlockIndex) end },
      { label = "[Tab]Next",   action = selectNextBlock },
      { label = "[V]iew",      action = toggleViewMode },
    })
    drawButtonRow(H, {
      { label = "[Spc]Tap",    action = function() if selectedBlockIndex > 0 then actionTapBlock(selectedBlockIndex) end end },
      { label = "[Arrows]Move",       action = nil },
      { label = "[Shift+Arr]Resize",  action = nil },
      { label = "[Q]uit",      action = actionQuit },
    })
  end
end

markDirty = function(part)
  if part == "all" then
    dirty.header = true
    dirty.body = true
    dirty.footer = true
  else
    dirty[part] = true
  end
end

redraw = function()
  if dirty.header then drawHeader(); dirty.header = false end
  if dirty.body then
    if appMode == "list" then drawList() else drawCanvas() end
    dirty.body = false
  end
  if dirty.footer then drawFooter(); dirty.footer = false end
end

-- Repaints the whole app UI immediately, used right after any modal dialog
-- closes so its box never lingers on screen (keeps things flicker-free
-- even across multi-step dialog flows). Safe to call directly since by
-- the time a dialog function returns, suspendRender has already been
-- reset to false.
refreshAfterDialog = function()
  markDirty("all")
  redraw()
end

setStatus = function(msg, color)
  statusMsg = msg or ""
  statusColor = color or colors.white
  statusExpireAt = os.clock() + 4
  markDirty("footer")
end

-- ======================================================================
-- TEXT INPUT PRIMITIVE (custom line editor, term API only)
-- ======================================================================
readLineInput = function(x, y, width, initial)
  local value = initial or ""
  local cursorPos = #value + 1

  local function render()
    term.setCursorPos(x, y)
    term.setBackgroundColor(colors.black)
    term.setTextColor(colors.white)
    local display = value
    local dispCursor = cursorPos
    if #display > width then
      local startPos = math.max(1, cursorPos - width + 1)
      display = value:sub(startPos, startPos + width - 1)
      dispCursor = cursorPos - startPos + 1
    end
    term.write(display .. string.rep(" ", width - #display))
    term.setCursorPos(x + math.min(dispCursor - 1, width - 1), y)
  end

  term.setCursorBlink(true)
  render()

  while true do
    local ev, p1 = os.pullEvent()
    if ev == "char" then
      value = value:sub(1, cursorPos - 1) .. p1 .. value:sub(cursorPos)
      cursorPos = cursorPos + 1
      render()
    elseif ev == "key" then
      if p1 == keys.backspace then
        if cursorPos > 1 then
          value = value:sub(1, cursorPos - 2) .. value:sub(cursorPos)
          cursorPos = cursorPos - 1
          render()
        end
      elseif p1 == keys.delete then
        value = value:sub(1, cursorPos - 1) .. value:sub(cursorPos + 1)
        render()
      elseif p1 == keys.left then
        if cursorPos > 1 then cursorPos = cursorPos - 1; render() end
      elseif p1 == keys.right then
        if cursorPos <= #value then cursorPos = cursorPos + 1; render() end
      elseif p1 == keys.home then
        cursorPos = 1; render()
      elseif p1 == keys["end"] then
        cursorPos = #value + 1; render()
      elseif p1 == keys.enter then
        term.setCursorBlink(false)
        return value
      elseif p1 == keys.escape then
        term.setCursorBlink(false)
        return nil
      end
    end
  end
end

-- ======================================================================
-- DIALOGS
-- Every dialog-opening function below sets suspendRender = true for its
-- duration (so the background render loop can't paint over it) and
-- guarantees that flag is cleared again even if something goes wrong,
-- via pcall acting as a try/finally.
-- ======================================================================

-- Generic multi-option modal. options = { { char="1", label="[1] Foo",
-- value=anything }, ... }. Returns the chosen value, or nil on Escape.
choiceDialog = function(title, message, options)
  suspendRender = true
  local function run()
    local boxW = math.min(W - 4, 46)
    local boxH = math.min(H - 2, 4 + #options + 1)
    local boxX = math.floor((W - boxW) / 2) + 1
    local boxY = math.max(1, math.floor((H - boxH) / 2) + 1)

    drawBox(boxX, boxY, boxW, boxH, title)

    term.setCursorPos(boxX + 1, boxY + 2)
    term.setBackgroundColor(colors.gray)
    term.setTextColor(colors.white)
    local msg = message
    if #msg > boxW - 2 then msg = msg:sub(1, boxW - 2) end
    term.write(msg)

    local buttons = {}
    for i, opt in ipairs(options) do
      local y = boxY + 3 + (i - 1)
      if y < boxY + boxH - 1 then
        term.setCursorPos(boxX + 1, y)
        term.setBackgroundColor(colors.gray)
        term.setTextColor(colors.yellow)
        local label = opt.label
        if #label > boxW - 2 then label = label:sub(1, boxW - 2) end
        term.write(label)
        buttons[#buttons + 1] = { x1 = boxX + 1, x2 = boxX + #label, y = y, value = opt.value, char = opt.char }
      end
    end

    term.setCursorPos(boxX + 1, boxY + boxH - 1)
    term.setBackgroundColor(colors.gray)
    term.setTextColor(colors.lightGray)
    term.write("[Esc] Cancel")

    while true do
      local ev, a, b, c = os.pullEvent()
      if ev == "key" and a == keys.escape then
        return nil
      elseif ev == "char" then
        for _, btn in ipairs(buttons) do
          if btn.char and a == btn.char then return btn.value end
        end
      elseif ev == "mouse_click" then
        local mx, my = b, c
        for _, btn in ipairs(buttons) do
          if my == btn.y and mx >= btn.x1 and mx <= btn.x2 then return btn.value end
        end
      end
    end
  end
  local ok, result = pcall(run)
  suspendRender = false
  if not ok then error(result, 0) end
  return result
end

promptSingleField = function(title, label, default)
  suspendRender = true
  local function run()
    local boxW = math.min(W - 4, 40)
    local boxX = math.floor((W - boxW) / 2) + 1
    local boxH = 5
    local boxY = math.max(1, math.floor((H - boxH) / 2) + 1)

    drawBox(boxX, boxY, boxW, boxH, title)
    term.setCursorPos(boxX + 1, boxY + 2)
    term.setBackgroundColor(colors.gray)
    term.setTextColor(colors.white)
    term.write(label)

    return readLineInput(boxX + 1, boxY + 3, boxW - 2, default or "")
  end
  local ok, result = pcall(run)
  suspendRender = false
  if not ok then error(result, 0) end
  return result
end

promptTwoFields = function(title, label1, default1, label2, default2)
  suspendRender = true
  local function run()
    local boxW = math.min(W - 4, 40)
    local boxX = math.floor((W - boxW) / 2) + 1
    local boxH = 7
    local boxY = math.max(1, math.floor((H - boxH) / 2) + 1)

    drawBox(boxX, boxY, boxW, boxH, title)

    term.setCursorPos(boxX + 1, boxY + 2)
    term.setBackgroundColor(colors.gray)
    term.setTextColor(colors.white)
    term.write(label1)
    local v1 = readLineInput(boxX + 1, boxY + 3, boxW - 2, default1 or "")
    if v1 == nil then return nil, nil end

    term.setCursorPos(boxX + 1, boxY + 4)
    term.setBackgroundColor(colors.gray)
    term.setTextColor(colors.white)
    term.write(label2)
    local v2 = readLineInput(boxX + 1, boxY + 5, boxW - 2, default2 or "")
    if v2 == nil then return nil, nil end

    return v1, v2
  end
  local ok, r1, r2 = pcall(run)
  suspendRender = false
  if not ok then error(r1, 0) end
  return r1, r2
end

-- Step 1 of "Add": choose Single vs Bundled link.
promptEntryKind = function()
  return choiceDialog(" Add New Link ", "What kind of link do you want to add?", {
    { char = "1", label = "[1] Single Link (input or output)", value = KIND_SINGLE },
    { char = "2", label = "[2] Bundled Link (Toggle + Status)", value = KIND_BUNDLE },
  })
end

-- Choose Input vs Output for a single link.
promptLinkMode = function(currentMode)
  local current = (currentMode == MODE_INPUT) and "Input" or "Output"
  return choiceDialog(" Link Type ", "Select link type (currently: " .. current .. "):", {
    { char = "1", label = "[1] Output - can send/toggle a signal", value = MODE_OUTPUT },
    { char = "2", label = "[2] Input - receive signal only", value = MODE_INPUT },
  })
end

-- Name + Frequency 1 + Frequency 2, used for single links.
promptNameAndFreqs = function(title, defaults)
  defaults = defaults or {}
  suspendRender = true
  local function run()
    local boxW = math.min(W - 4, 42)
    local boxX = math.floor((W - boxW) / 2) + 1
    local boxH = 9
    local boxY = math.max(1, math.floor((H - boxH) / 2) + 1)
    local innerW = boxW - 2

    drawBox(boxX, boxY, boxW, boxH, title)

    term.setCursorPos(boxX + 1, boxY + 2)
    term.setBackgroundColor(colors.gray)
    term.setTextColor(colors.white)
    term.write("Name:")
    local name = readLineInput(boxX + 1, boxY + 3, innerW, defaults.name or "")
    if name == nil then return nil end
    name = trim(name)
    if name == "" then
      setStatus("Name cannot be empty. Cancelled.", colors.red)
      return nil
    end

    term.setCursorPos(boxX + 1, boxY + 4)
    term.setBackgroundColor(colors.gray)
    term.setTextColor(colors.white)
    term.write("Frequency 1:")
    local f1 = readLineInput(boxX + 1, boxY + 5, innerW, defaults.freq1 and tostring(defaults.freq1) or "")
    if f1 == nil then return nil end
    f1 = trim(f1)
    if f1 == "" then
      setStatus("Frequency 1 cannot be empty. Cancelled.", colors.red)
      return nil
    end

    term.setCursorPos(boxX + 1, boxY + 6)
    term.setBackgroundColor(colors.gray)
    term.setTextColor(colors.white)
    term.write("Frequency 2:")
    local f2 = readLineInput(boxX + 1, boxY + 7, innerW, defaults.freq2 and tostring(defaults.freq2) or "")
    if f2 == nil then return nil end
    f2 = trim(f2)
    if f2 == "" then
      setStatus("Frequency 2 cannot be empty. Cancelled.", colors.red)
      return nil
    end

    return { name = name, freq1 = f1, freq2 = f2 }
  end
  local ok, result = pcall(run)
  suspendRender = false
  if not ok then error(result, 0) end
  return result
end

-- Full Add/Edit flow for a single link: mode, then name+freqs.
-- Returns { mode=, name=, freq1=, freq2= } or nil if cancelled at any step.
singleLinkFullEditFlow = function(existing)
  local mode = promptLinkMode(existing and existing.mode or MODE_OUTPUT)
  refreshAfterDialog()
  if mode == nil then return nil end

  local fields = promptNameAndFreqs(existing and " Edit Link " or " Add Single Link ", existing)
  refreshAfterDialog()
  if fields == nil then return nil end

  fields.mode = mode
  return fields
end

-- Full Add/Edit flow for a bundle: name, then Toggle freqs, then Status freqs.
-- Returns { name=, toggleFreq1=, toggleFreq2=, statusFreq1=, statusFreq2= } or nil.
bundleFullEditFlow = function(existing)
  local name = promptSingleField(existing and " Edit Bundle Name " or " Add Bundled Link ",
    "Bundle Name:", existing and existing.name or "")
  refreshAfterDialog()
  if name == nil then return nil end
  name = trim(name)
  if name == "" then
    setStatus("Name cannot be empty. Cancelled.", colors.red)
    return nil
  end

  local tf1, tf2 = promptTwoFields(" Toggle Link Frequencies ",
    "Toggle Frequency 1:", existing and tostring(existing.toggle.freq1) or "",
    "Toggle Frequency 2:", existing and tostring(existing.toggle.freq2) or "")
  refreshAfterDialog()
  if tf1 == nil then return nil end
  tf1, tf2 = trim(tf1), trim(tf2)
  if tf1 == "" or tf2 == "" then
    setStatus("Toggle frequencies cannot be empty. Cancelled.", colors.red)
    return nil
  end

  local sf1, sf2 = promptTwoFields(" Status Link Frequencies ",
    "Status Frequency 1:", existing and tostring(existing.status.freq1) or "",
    "Status Frequency 2:", existing and tostring(existing.status.freq2) or "")
  refreshAfterDialog()
  if sf1 == nil then return nil end
  sf1, sf2 = trim(sf1), trim(sf2)
  if sf1 == "" or sf2 == "" then
    setStatus("Status frequencies cannot be empty. Cancelled.", colors.red)
    return nil
  end

  return {
    name = name,
    toggleFreq1 = tf1, toggleFreq2 = tf2,
    statusFreq1 = sf1, statusFreq2 = sf2,
  }
end

confirmDialog = function(message)
  suspendRender = true
  local function run()
    local boxW = math.min(W - 4, math.max(24, #message + 4))
    local boxX = math.floor((W - boxW) / 2) + 1
    local boxH = 5
    local boxY = math.max(1, math.floor((H - boxH) / 2) + 1)

    drawBox(boxX, boxY, boxW, boxH, " Confirm ")
    term.setCursorPos(boxX + 1, boxY + 2)
    term.setBackgroundColor(colors.gray)
    term.setTextColor(colors.white)
    local msg = message
    if #msg > boxW - 2 then msg = msg:sub(1, boxW - 2) end
    term.write(msg)
    term.setCursorPos(boxX + 1, boxY + 3)
    term.setTextColor(colors.lightGray)
    term.write("[Y] Yes    [N] No")

    while true do
      local ev, key = os.pullEvent("key")
      if key == keys.y then return true
      elseif key == keys.n or key == keys.escape then return false end
    end
  end
  local ok, result = pcall(run)
  suspendRender = false
  if not ok then error(result, 0) end
  return result
end

-- Scrollable single-select list of link/member candidates for binding a
-- canvas block. Returns the chosen candidate table, or nil on cancel.
pickLinkDialog = function(title, candidates, initialIndex)
  if #candidates == 0 then return nil end
  suspendRender = true
  local function run()
    local boxW = math.max(20, math.min(W - 4, 46))
    local boxH = math.max(6, math.min(H - 2, 14))
    local boxX = math.floor((W - boxW) / 2) + 1
    local boxY = math.max(1, math.floor((H - boxH) / 2) + 1)
    local innerTop = boxY + 2
    local innerBottom = boxY + boxH - 2
    local visibleRows = math.max(1, innerBottom - innerTop + 1)
    local sel = clamp(initialIndex or 1, 1, #candidates)
    local scroll = 0

    local function ensureVis()
      if sel <= scroll then scroll = sel - 1
      elseif sel > scroll + visibleRows then scroll = sel - visibleRows end
      scroll = clamp(scroll, 0, math.max(0, #candidates - visibleRows))
    end
    ensureVis()

    local function render()
      drawBox(boxX, boxY, boxW, boxH, title)
      for row = 0, visibleRows - 1 do
        local y = innerTop + row
        local idx = scroll + row + 1
        term.setCursorPos(boxX + 1, y)
        if idx <= #candidates then
          local isSel = idx == sel
          term.setBackgroundColor(isSel and colors.lightBlue or colors.gray)
          term.setTextColor(isSel and colors.black or colors.white)
          local label = candidates[idx].label
          if #label > boxW - 2 then label = label:sub(1, boxW - 3) .. "~" end
          term.write(label .. string.rep(" ", boxW - 2 - #label))
        else
          term.setBackgroundColor(colors.gray)
          term.write(string.rep(" ", boxW - 2))
        end
      end
      term.setCursorPos(boxX + 1, boxY + boxH - 1)
      term.setBackgroundColor(colors.gray)
      term.setTextColor(colors.lightGray)
      term.write("[Enter]Select [Esc]Cancel")
    end
    render()

    while true do
      local ev, a, b, c = os.pullEvent()
      if ev == "key" then
        if a == keys.up then
          if sel > 1 then sel = sel - 1; ensureVis(); render() end
        elseif a == keys.down then
          if sel < #candidates then sel = sel + 1; ensureVis(); render() end
        elseif a == keys.enter then
          return candidates[sel]
        elseif a == keys.escape then
          return nil
        end
      elseif ev == "mouse_click" then
        local mx, my = b, c
        if my >= innerTop and my <= innerBottom then
          local idx = scroll + (my - innerTop) + 1
          if candidates[idx] then return candidates[idx] end
        end
      elseif ev == "mouse_scroll" then
        sel = clamp(sel + a, 1, #candidates); ensureVis(); render()
      end
    end
  end
  local ok, result = pcall(run)
  suspendRender = false
  if not ok then error(result, 0) end
  return result
end

-- Editor for an Output block's value->text map (values 0-15). Backspace
-- clears the highlighted value's label; Enter opens a text prompt for it.
-- Returns the updated labels table (edits are committed as you go).
labelsEditorDialog = function(existing)
  suspendRender = true
  local function run()
    local labels = {}
    for k, v in pairs(existing or {}) do labels[k] = v end

    local boxW = math.max(20, math.min(W - 4, 40))
    local boxH = math.max(6, math.min(H - 2, 18))
    local boxX = math.floor((W - boxW) / 2) + 1
    local boxY = math.max(1, math.floor((H - boxH) / 2) + 1)
    local innerTop = boxY + 2
    local innerBottom = boxY + boxH - 2
    local visibleRows = math.max(1, innerBottom - innerTop + 1)
    local sel = 1 -- 1..16, representing signal values 0..15
    local scroll = 0

    local function ensureVis()
      if sel <= scroll then scroll = sel - 1
      elseif sel > scroll + visibleRows then scroll = sel - visibleRows end
      scroll = clamp(scroll, 0, math.max(0, 16 - visibleRows))
    end
    ensureVis()

    local function render()
      drawBox(boxX, boxY, boxW, boxH, " Edit Value Labels ")
      for row = 0, visibleRows - 1 do
        local y = innerTop + row
        local valueIdx = scroll + row
        term.setCursorPos(boxX + 1, y)
        if valueIdx <= 15 then
          local isSel = (valueIdx + 1) == sel
          term.setBackgroundColor(isSel and colors.lightBlue or colors.gray)
          term.setTextColor(isSel and colors.black or colors.white)
          local labelTxt = labels[valueIdx] or "(number)"
          local line = string.format("%2d: %s", valueIdx, labelTxt)
          if #line > boxW - 2 then line = line:sub(1, boxW - 3) .. "~" end
          term.write(line .. string.rep(" ", boxW - 2 - #line))
        else
          term.setBackgroundColor(colors.gray)
          term.write(string.rep(" ", boxW - 2))
        end
      end
      term.setCursorPos(boxX + 1, boxY + boxH - 1)
      term.setBackgroundColor(colors.gray)
      term.setTextColor(colors.lightGray)
      term.write("[Ent]Set [Bksp]Clear [X]Done")
    end
    render()

    while true do
      local ev, a, b, c = os.pullEvent()
      if ev == "key" then
        if a == keys.up then
          if sel > 1 then sel = sel - 1; ensureVis(); render() end
        elseif a == keys.down then
          if sel < 16 then sel = sel + 1; ensureVis(); render() end
        elseif a == keys.enter then
          local valueIdx = sel - 1
          local newText = promptSingleField(" Label for value " .. valueIdx .. " ", "Text (blank = clear):", labels[valueIdx] or "")
          suspendRender = true -- promptSingleField reset this to false on return; we're still inside our own dialog
          if newText ~= nil then
            newText = trim(newText)
            labels[valueIdx] = (newText ~= "") and newText or nil
          end
          render()
        elseif a == keys.backspace then
          labels[sel - 1] = nil
          render()
        elseif a == keys.x or a == keys.escape then
          return labels
        end
      elseif ev == "mouse_click" then
        local mx, my = b, c
        if my >= innerTop and my <= innerBottom then
          local valueIdx = scroll + (my - innerTop)
          if valueIdx <= 15 then sel = valueIdx + 1; ensureVis(); render() end
        end
      elseif ev == "mouse_scroll" then
        sel = clamp(sel + a, 1, 16); ensureVis(); render()
      end
    end
  end
  local ok, result = pcall(run)
  suspendRender = false
  if not ok then error(result, 0) end
  return result
end

-- ======================================================================
-- OUTPUT CONTROL
-- ======================================================================
applyOutput = function(pollable, value)
  pollable.output = clamp(value, 0, 15)
  local ok = safeSendSignal(pollable.freq1, pollable.freq2, pollable.output)
  if not ok then
    setStatus("Bridge offline - output stored, will resend on reconnect.", colors.red)
  end
  dataDirty = true
  markDirty("body")
end

-- Returns the pollable table to toggle/inc/dec for the current list-view
-- selection, or nil if the selected row is Input-mode / a Status link. A
-- bundle's title row and its Toggle sub-row both resolve to the same
-- Toggle link, so you can toggle the group directly from the title bar.
getTogglablePollable = function()
  local row = getSelectedRow()
  if not row then return nil end
  local entry = links[row.linkIndex]
  if row.rowType == "single" then
    if entry.mode == MODE_OUTPUT then return entry end
    return nil
  elseif row.rowType == "bundleToggle" or row.rowType == "bundleHeader" then
    return entry.toggle
  end
  return nil
end

-- ======================================================================
-- LINK ACTIONS (list view)
-- ======================================================================
actionAdd = function()
  local kind = promptEntryKind()
  refreshAfterDialog()
  if kind == nil then return end

  if kind == KIND_SINGLE then
    local result = singleLinkFullEditFlow(nil)
    if not result then return end
    links[#links + 1] = {
      id = nextLinkId, kind = KIND_SINGLE, name = result.name, mode = result.mode,
      freq1 = result.freq1, freq2 = result.freq2, output = 0, input = 0,
    }
    nextLinkId = nextLinkId + 1
    dataDirty = true
    refreshDisplayRows()
    selectEntryByLinkIndex(#links)
    setStatus("Added " .. (result.mode == MODE_OUTPUT and "output" or "input") ..
      " link '" .. result.name .. "'.", colors.lime)
  else
    local result = bundleFullEditFlow(nil)
    if not result then return end
    links[#links + 1] = {
      id = nextLinkId, kind = KIND_BUNDLE, name = result.name, expanded = true,
      toggle = { mode = MODE_OUTPUT, freq1 = result.toggleFreq1, freq2 = result.toggleFreq2, output = 0, input = 0 },
      status = { mode = MODE_INPUT, freq1 = result.statusFreq1, freq2 = result.statusFreq2, output = 0, input = 0 },
    }
    nextLinkId = nextLinkId + 1
    dataDirty = true
    refreshDisplayRows()
    selectEntryByLinkIndex(#links)
    setStatus("Added bundled link '" .. result.name .. "'.", colors.lime)
  end
end

actionDelete = function()
  local row = getSelectedRow()
  if not row then
    setStatus("No link selected.", colors.orange)
    return
  end
  local entry = links[row.linkIndex]
  local label = (entry.kind == KIND_BUNDLE)
    and ("bundle '" .. entry.name .. "' (Toggle + Status)")
    or ("'" .. entry.name .. "'")
  local confirmed = confirmDialog("Delete " .. label .. "? This cannot be undone.")
  refreshAfterDialog()
  if confirmed then
    if entry.kind == KIND_SINGLE then
      if entry.mode == MODE_OUTPUT then
        safeSendSignal(entry.freq1, entry.freq2, 0) -- zero the output before removing
      end
    else
      safeSendSignal(entry.toggle.freq1, entry.toggle.freq2, 0)
    end
    table.remove(links, row.linkIndex)
    dataDirty = true
    refreshDisplayRows()
    setStatus("Deleted. Any canvas blocks bound to it now show (unbound).", colors.orange)
  end
end

actionRename = function()
  local row = getSelectedRow()
  if not row then
    setStatus("No link selected.", colors.orange)
    return
  end
  local entry = links[row.linkIndex]
  local newName = promptSingleField(" Rename ", "Name:", entry.name)
  refreshAfterDialog()
  if newName == nil then return end
  newName = trim(newName)
  if newName == "" then
    setStatus("Name cannot be empty.", colors.red)
    return
  end
  entry.name = newName
  dataDirty = true
  refreshDisplayRows()
  selectEntryByLinkIndex(row.linkIndex)
  setStatus("Renamed to '" .. newName .. "'.", colors.lime)
end

-- Edits only the frequency pair(s) relevant to the currently selected row.
actionEditFrequencies = function()
  local row = getSelectedRow()
  if not row then
    setStatus("No link selected.", colors.orange)
    return
  end
  local entry = links[row.linkIndex]

  if row.rowType == "single" then
    local f1, f2 = promptTwoFields(" Edit Frequencies ",
      "Frequency 1:", tostring(entry.freq1), "Frequency 2:", tostring(entry.freq2))
    refreshAfterDialog()
    if f1 == nil then return end
    f1, f2 = trim(f1), trim(f2)
    if f1 == "" or f2 == "" then
      setStatus("Frequencies cannot be empty.", colors.red)
      return
    end
    entry.freq1, entry.freq2 = f1, f2
    dataDirty = true
    setStatus("Frequencies updated for '" .. entry.name .. "'.", colors.lime)

  elseif row.rowType == "bundleToggle" then
    local f1, f2 = promptTwoFields(" Edit Toggle Frequencies ",
      "Toggle Frequency 1:", tostring(entry.toggle.freq1), "Toggle Frequency 2:", tostring(entry.toggle.freq2))
    refreshAfterDialog()
    if f1 == nil then return end
    f1, f2 = trim(f1), trim(f2)
    if f1 == "" or f2 == "" then
      setStatus("Frequencies cannot be empty.", colors.red)
      return
    end
    entry.toggle.freq1, entry.toggle.freq2 = f1, f2
    dataDirty = true
    setStatus("Toggle frequencies updated for '" .. entry.name .. "'.", colors.lime)

  elseif row.rowType == "bundleStatus" then
    local f1, f2 = promptTwoFields(" Edit Status Frequencies ",
      "Status Frequency 1:", tostring(entry.status.freq1), "Status Frequency 2:", tostring(entry.status.freq2))
    refreshAfterDialog()
    if f1 == nil then return end
    f1, f2 = trim(f1), trim(f2)
    if f1 == "" or f2 == "" then
      setStatus("Frequencies cannot be empty.", colors.red)
      return
    end
    entry.status.freq1, entry.status.freq2 = f1, f2
    dataDirty = true
    setStatus("Status frequencies updated for '" .. entry.name .. "'.", colors.lime)

  else -- bundleHeader: edit both members in one go
    local tf1, tf2 = promptTwoFields(" Edit Toggle Frequencies ",
      "Toggle Frequency 1:", tostring(entry.toggle.freq1), "Toggle Frequency 2:", tostring(entry.toggle.freq2))
    refreshAfterDialog()
    if tf1 == nil then return end
    tf1, tf2 = trim(tf1), trim(tf2)
    if tf1 == "" or tf2 == "" then
      setStatus("Frequencies cannot be empty.", colors.red)
      return
    end

    local sf1, sf2 = promptTwoFields(" Edit Status Frequencies ",
      "Status Frequency 1:", tostring(entry.status.freq1), "Status Frequency 2:", tostring(entry.status.freq2))
    refreshAfterDialog()
    if sf1 == nil then return end
    sf1, sf2 = trim(sf1), trim(sf2)
    if sf1 == "" or sf2 == "" then
      setStatus("Frequencies cannot be empty.", colors.red)
      return
    end

    entry.toggle.freq1, entry.toggle.freq2 = tf1, tf2
    entry.status.freq1, entry.status.freq2 = sf1, sf2
    dataDirty = true
    setStatus("Frequencies updated for bundle '" .. entry.name .. "'.", colors.lime)
  end
end

-- Full edit: name/type/freqs for a single link, or name+both freq pairs for a bundle.
actionEditFull = function()
  local row = getSelectedRow()
  if not row then
    setStatus("No link selected.", colors.orange)
    return
  end
  local entry = links[row.linkIndex]

  if entry.kind == KIND_SINGLE then
    local result = singleLinkFullEditFlow(entry)
    if not result then return end
    local modeChanged = result.mode ~= entry.mode
    if modeChanged and entry.mode == MODE_OUTPUT then
      safeSendSignal(entry.freq1, entry.freq2, 0) -- release the old output
    end
    entry.name, entry.mode, entry.freq1, entry.freq2 = result.name, result.mode, result.freq1, result.freq2
    if modeChanged then
      entry.output = 0
      entry.input = 0
    end
    dataDirty = true
    refreshDisplayRows()
    selectEntryByLinkIndex(row.linkIndex)
    setStatus("Updated link '" .. entry.name .. "'.", colors.lime)
  else
    local result = bundleFullEditFlow(entry)
    if not result then return end
    entry.name = result.name
    entry.toggle.freq1, entry.toggle.freq2 = result.toggleFreq1, result.toggleFreq2
    entry.status.freq1, entry.status.freq2 = result.statusFreq1, result.statusFreq2
    dataDirty = true
    refreshDisplayRows()
    selectEntryByLinkIndex(row.linkIndex)
    setStatus("Updated bundle '" .. entry.name .. "'.", colors.lime)
  end
end

actionDuplicate = function()
  local row = getSelectedRow()
  if not row then
    setStatus("No link selected.", colors.orange)
    return
  end
  local entry = links[row.linkIndex]
  local copy
  if entry.kind == KIND_SINGLE then
    copy = {
      id = nextLinkId, kind = KIND_SINGLE, name = entry.name .. " (copy)", mode = entry.mode,
      freq1 = entry.freq1, freq2 = entry.freq2, output = 0, input = 0,
    }
  else
    copy = {
      id = nextLinkId, kind = KIND_BUNDLE, name = entry.name .. " (copy)", expanded = true,
      toggle = { mode = MODE_OUTPUT, freq1 = entry.toggle.freq1, freq2 = entry.toggle.freq2, output = 0, input = 0 },
      status = { mode = MODE_INPUT, freq1 = entry.status.freq1, freq2 = entry.status.freq2, output = 0, input = 0 },
    }
  end
  nextLinkId = nextLinkId + 1
  table.insert(links, row.linkIndex + 1, copy)
  dataDirty = true
  refreshDisplayRows()
  selectEntryByLinkIndex(row.linkIndex + 1)
  setStatus("Duplicated '" .. entry.name .. "'.", colors.lime)
end

actionToggleOutput = function()
  local target = getTogglablePollable()
  if not target then
    setStatus("This link is input-only and cannot be toggled.", colors.orange)
    return
  end
  applyOutput(target, target.output > 0 and 0 or 15)
end

actionIncOutput = function()
  local target = getTogglablePollable()
  if not target then
    setStatus("This link is input-only and cannot be toggled.", colors.orange)
    return
  end
  applyOutput(target, target.output + 1)
end

actionDecOutput = function()
  local target = getTogglablePollable()
  if not target then
    setStatus("This link is input-only and cannot be toggled.", colors.orange)
    return
  end
  applyOutput(target, target.output - 1)
end

actionFilter = function()
  local text = promptSingleField(" Search / Filter ", "Name contains (blank = show all):", filterText)
  refreshAfterDialog()
  if text == nil then return end
  filterText = trim(text)
  refreshDisplayRows()
  setStatus(filterText ~= "" and ("Filter: " .. filterText) or "Filter cleared.", colors.lightBlue)
end

-- ======================================================================
-- CANVAS BLOCK ACTIONS
-- ======================================================================
actionAddBlock = function()
  local blockType = choiceDialog(" Add Block ", "What kind of block do you want to add?", {
    { char = "1", label = "[1] Text - a movable label", value = BLOCK_TEXT },
    { char = "2", label = "[2] Input - read-only value display", value = BLOCK_INPUT },
    { char = "3", label = "[3] Output - toggle/send a value", value = BLOCK_OUTPUT },
  })
  refreshAfterDialog()
  if blockType == nil then return end

  local block = { type = blockType, text = "", label = "", linkId = nil, memberKey = nil, labels = {} }

  if blockType == BLOCK_TEXT then
    local text = promptSingleField(" New Text Block ", "Text:", "Label")
    refreshAfterDialog()
    if text == nil then return end
    block.text = text
    block.w, block.h = DEFAULT_TEXT_W, DEFAULT_TEXT_H
  else
    local candidates = buildCandidates(blockType)
    if #candidates == 0 then
      setStatus("No suitable links exist yet. Add one from List view first.", colors.orange)
      return
    end
    local picked = pickLinkDialog(blockType == BLOCK_OUTPUT and " Bind Output To " or " Bind Input To ", candidates, 1)
    refreshAfterDialog()
    if picked == nil then return end
    block.linkId = picked.linkId
    block.memberKey = picked.memberKey
    local customLabel = promptSingleField(" Block Label ", "Custom label (blank = use link name):", "")
    refreshAfterDialog()
    block.label = customLabel and trim(customLabel) or ""
    block.w, block.h = DEFAULT_WIDGET_W, DEFAULT_WIDGET_H
  end

  -- Cascade new blocks diagonally so they don't perfectly stack on top of
  -- each other by default.
  local cascade = #canvasBlocks % 6
  block.x = clamp(2 + cascade * 2, 1, math.max(1, W - block.w + 1))
  block.y = clamp(LIST_TOP + cascade, LIST_TOP, math.max(LIST_TOP, LIST_BOTTOM - block.h + 1))

  canvasBlocks[#canvasBlocks + 1] = block
  selectedBlockIndex = #canvasBlocks
  dataDirty = true
  markDirty("body")
  setStatus("Block added. Drag it to reposition, or press Enter to edit.", colors.lime)
end

actionEditBlock = function(idx)
  local block = canvasBlocks[idx]
  if not block then
    setStatus("No block selected.", colors.orange)
    return
  end

  if block.type == BLOCK_TEXT then
    local newText = promptSingleField(" Edit Text Block ", "Text:", block.text or "")
    refreshAfterDialog()
    if newText == nil then return end
    block.text = newText
    dataDirty = true
    setStatus("Text block updated.", colors.lime)
    return
  end

  local candidates = buildCandidates(block.type)
  if #candidates == 0 then
    setStatus("No suitable links exist to bind to.", colors.orange)
    return
  end
  local currentPick = 1
  for i, cand in ipairs(candidates) do
    if cand.linkId == block.linkId and cand.memberKey == block.memberKey then currentPick = i; break end
  end
  local picked = pickLinkDialog(block.type == BLOCK_OUTPUT and " Bind Output To " or " Bind Input To ", candidates, currentPick)
  refreshAfterDialog()
  if picked then
    block.linkId = picked.linkId
    block.memberKey = picked.memberKey
  end

  local newLabel = promptSingleField(" Block Label ", "Custom label (blank = use link name):", block.label or "")
  refreshAfterDialog()
  if newLabel ~= nil then block.label = trim(newLabel) end

  if block.type == BLOCK_OUTPUT then
    local wantsLabels = confirmDialog("Set custom text for specific output values?")
    refreshAfterDialog()
    if wantsLabels then
      block.labels = labelsEditorDialog(block.labels or {})
      refreshAfterDialog()
    end
  end

  dataDirty = true
  setStatus("Block updated.", colors.lime)
end

actionDeleteBlock = function()
  if selectedBlockIndex == 0 or not canvasBlocks[selectedBlockIndex] then
    setStatus("No block selected.", colors.orange)
    return
  end
  local confirmed = confirmDialog("Remove this block from the canvas?")
  refreshAfterDialog()
  if confirmed then
    table.remove(canvasBlocks, selectedBlockIndex)
    selectedBlockIndex = 0
    dataDirty = true
    markDirty("body")
    setStatus("Block removed. The underlying link is unaffected.", colors.orange)
  end
end

-- The "tap" action for a block: a click/keypress that didn't drag it.
actionTapBlock = function(idx)
  local block = canvasBlocks[idx]
  if not block then return end
  if block.type == BLOCK_OUTPUT then
    local pollable, canWrite = resolveBlockSource(block)
    if pollable and canWrite then
      applyOutput(pollable, pollable.output > 0 and 0 or 15)
    else
      setStatus("This output block isn't bound to a writable link. Press Enter to configure.", colors.orange)
    end
  else
    -- Input blocks are read-only, so tapping opens their configuration
    -- instead - this is how you "change" an Input block. Text blocks
    -- open their text editor.
    actionEditBlock(idx)
  end
end

selectNextBlock = function()
  if #canvasBlocks == 0 then
    selectedBlockIndex = 0
    return
  end
  selectedBlockIndex = (selectedBlockIndex % #canvasBlocks) + 1
  markDirty("body")
  setStatus("Selected: " .. getBlockDisplayName(canvasBlocks[selectedBlockIndex]), colors.lightBlue)
end

-- Re-clamps every block's position/size to fit the current screen. Used
-- after a term_resize event so blocks can never end up off-screen.
clampAllBlocksToScreen = function()
  for _, block in ipairs(canvasBlocks) do
    local minW = (block.type == BLOCK_TEXT) and MIN_TEXT_W or MIN_WIDGET_W
    local minH = (block.type == BLOCK_TEXT) and MIN_TEXT_H or MIN_WIDGET_H
    block.w = clamp(block.w, minW, W)
    block.h = clamp(block.h, minH, math.max(minH, LIST_BOTTOM - LIST_TOP + 1))
    block.x = clamp(block.x, 1, math.max(1, W - block.w + 1))
    block.y = clamp(block.y, LIST_TOP, math.max(LIST_TOP, LIST_BOTTOM - block.h + 1))
  end
end

-- ======================================================================
-- EVENT HANDLERS (list view)
-- ======================================================================

-- isHeld is the 3rd value CC:Tweaked's "key" event provides: true means
-- this is an auto-repeat resend from the key still being held down, not
-- a fresh press. Navigation keeps repeating so holding an arrow scrolls
-- smoothly; every discrete action below is gated to fire only once per
-- physical press so a slightly-long press can't double-fire and cancel
-- itself out.
handleKey = function(key, isHeld)
  if key == keys.up then
    if selected > 1 then selected = selected - 1; ensureVisible(); markDirty("body") end
    return
  elseif key == keys.down then
    if selected < #displayRows then selected = selected + 1; ensureVisible(); markDirty("body") end
    return
  elseif key == keys.pageUp then
    if #displayRows > 0 then
      selected = math.max(1, selected - LIST_HEIGHT); ensureVisible(); markDirty("body")
    end
    return
  elseif key == keys.pageDown then
    if #displayRows > 0 then
      selected = math.min(#displayRows, selected + LIST_HEIGHT); ensureVisible(); markDirty("body")
    end
    return
  end

  if isHeld then return end -- ignore auto-repeat for everything below

  if key == keys.left then
    local row = getSelectedRow()
    if row then
      local entry = links[row.linkIndex]
      if entry.kind == KIND_BUNDLE and entry.expanded ~= false then
        toggleBundleExpanded(row.linkIndex)
      end
    end
  elseif key == keys.right then
    local row = getSelectedRow()
    if row then
      local entry = links[row.linkIndex]
      if entry.kind == KIND_BUNDLE and entry.expanded == false then
        toggleBundleExpanded(row.linkIndex)
      end
    end
  elseif key == keys.enter then
    actionEditFull()
  elseif key == keys.a then
    actionAdd()
  elseif key == keys.d then
    actionDelete()
  elseif key == keys.r then
    actionRename()
  elseif key == keys.e then
    actionEditFrequencies()
  elseif key == keys.space then
    actionToggleOutput()
  elseif key == keys.f then
    actionFilter()
  elseif key == keys.s then
    sortLinksAlpha()
  elseif key == keys.c then
    actionDuplicate()
  elseif key == keys.numPadAdd then
    actionIncOutput()
  elseif key == keys.numPadSubtract then
    actionDecOutput()
  end
end

-- The "char" event has no held/repeat flag, so +/- get a short manual
-- debounce instead to prevent a held key from spamming increments.
handleChar = function(ch)
  if ch == "+" or ch == "-" then
    local now = os.clock()
    if now - (charDebounce[ch] or 0) < CHAR_DEBOUNCE_INTERVAL then return end
    charDebounce[ch] = now
    if ch == "+" then actionIncOutput() else actionDecOutput() end
  end
end

handleMouseClick = function(button, x, y)
  if button ~= 1 then return end

  for _, btn in ipairs(footerButtons) do
    if y == btn.y and x >= btn.x1 and x <= btn.x2 then
      if btn.action then btn.action() end
      return
    end
  end

  if y >= LIST_TOP and y <= LIST_BOTTOM then
    for _, zone in ipairs(rowClickZones) do
      if y == zone.y and x >= zone.x1 and x <= zone.x2 then
        if zone.kind == "expand" then
          toggleBundleExpanded(zone.linkIndex)
        elseif zone.kind == "toggleGroup" then
          selectEntryByLinkIndex(zone.linkIndex)
          actionToggleOutput()
        end
        return
      end
    end

    local row = y - LIST_TOP
    local ri = scrollOffset + row + 1
    if displayRows[ri] then
      selected = ri
      markDirty("body")
    end
  end
end

handleMouseScroll = function(dir, x, y)
  if #displayRows == 0 then return end
  selected = clamp(selected + dir * 3, 1, #displayRows)
  ensureVisible()
  markDirty("body")
end

-- ======================================================================
-- EVENT HANDLERS (canvas view)
-- ======================================================================
handleCanvasKey = function(key, isHeld)
  if key == keys.up or key == keys.down or key == keys.left or key == keys.right then
    if selectedBlockIndex == 0 then return end
    local block = canvasBlocks[selectedBlockIndex]
    if not block then return end
    local minW = (block.type == BLOCK_TEXT) and MIN_TEXT_W or MIN_WIDGET_W
    local minH = (block.type == BLOCK_TEXT) and MIN_TEXT_H or MIN_WIDGET_H
    if isShiftDown then
      if key == keys.right then block.w = clamp(block.w + 1, minW, W - block.x + 1)
      elseif key == keys.left then block.w = clamp(block.w - 1, minW, W - block.x + 1)
      elseif key == keys.down then block.h = clamp(block.h + 1, minH, LIST_BOTTOM - block.y + 1)
      elseif key == keys.up then block.h = clamp(block.h - 1, minH, LIST_BOTTOM - block.y + 1) end
    else
      if key == keys.right then block.x = clamp(block.x + 1, 1, W - block.w + 1)
      elseif key == keys.left then block.x = clamp(block.x - 1, 1, W - block.w + 1)
      elseif key == keys.down then block.y = clamp(block.y + 1, LIST_TOP, LIST_BOTTOM - block.h + 1)
      elseif key == keys.up then block.y = clamp(block.y - 1, LIST_TOP, LIST_BOTTOM - block.h + 1) end
    end
    dataDirty = true
    markDirty("body")
    return
  end

  if isHeld then return end -- discrete actions ignore key-repeat

  if key == keys.n then
    actionAddBlock()
  elseif key == keys.d then
    actionDeleteBlock()
  elseif key == keys.enter then
    actionEditBlock(selectedBlockIndex)
  elseif key == keys.tab then
    selectNextBlock()
  elseif key == keys.space then
    if selectedBlockIndex > 0 then actionTapBlock(selectedBlockIndex) end
  end
end

handleCanvasMouseClick = function(button, x, y)
  for _, btn in ipairs(footerButtons) do
    if y == btn.y and x >= btn.x1 and x <= btn.x2 then
      if btn.action then btn.action() end
      return
    end
  end

  if button == 1 then
    local idx = findBlockAt(x, y)
    if idx then
      selectedBlockIndex = idx
      local block = canvasBlocks[idx]
      local handleX, handleY = block.x + block.w - 1, block.y + block.h - 1
      if x == handleX and y == handleY then
        dragState = { mode = "resize", blockIndex = idx, startMouseX = x, startMouseY = y, startW = block.w, startH = block.h, moved = false }
      else
        dragState = { mode = "move", blockIndex = idx, startMouseX = x, startMouseY = y, startX = block.x, startY = block.y, moved = false }
      end
    else
      selectedBlockIndex = 0
      dragState = nil
    end
    markDirty("body")
  elseif button == 2 then
    local idx = findBlockAt(x, y)
    if idx then
      selectedBlockIndex = idx
      actionEditBlock(idx)
    end
  end
end

handleCanvasMouseDrag = function(button, x, y)
  if button ~= 1 or not dragState then return end
  local block = canvasBlocks[dragState.blockIndex]
  if not block then dragState = nil; return end

  local dx = x - dragState.startMouseX
  local dy = y - dragState.startMouseY
  if dx ~= 0 or dy ~= 0 then dragState.moved = true end

  if dragState.mode == "move" then
    block.x = clamp(dragState.startX + dx, 1, math.max(1, W - block.w + 1))
    block.y = clamp(dragState.startY + dy, LIST_TOP, math.max(LIST_TOP, LIST_BOTTOM - block.h + 1))
  else
    local minW = (block.type == BLOCK_TEXT) and MIN_TEXT_W or MIN_WIDGET_W
    local minH = (block.type == BLOCK_TEXT) and MIN_TEXT_H or MIN_WIDGET_H
    block.w = clamp(dragState.startW + dx, minW, W - block.x + 1)
    block.h = clamp(dragState.startH + dy, minH, LIST_BOTTOM - block.y + 1)
  end
  markDirty("body")
end

-- On release: a "move" drag that ended within one character cell of
-- where it started is treated as a tap, not a move - the block snaps
-- back to its exact starting position and its tap action fires. This
-- tolerates the small amount of cursor drift that's very easy to get
-- with a mouse in Minecraft, which previously made a perfectly good
-- click silently count as "the block moved" and cancel the tap.
handleCanvasMouseUp = function(button, x, y)
  if button ~= 1 or not dragState then return end
  local block = canvasBlocks[dragState.blockIndex]
  if not block then
    dragState = nil
    markDirty("body")
    return
  end

  if dragState.mode == "move" then
    local dx = math.abs(x - dragState.startMouseX)
    local dy = math.abs(y - dragState.startMouseY)
    if dx <= 1 and dy <= 1 then
      block.x, block.y = dragState.startX, dragState.startY
      dragState = nil
      markDirty("body")
      actionTapBlock(block == canvasBlocks[selectedBlockIndex] and selectedBlockIndex or nil)
      return
    else
      dataDirty = true
    end
  elseif dragState.mode == "resize" and dragState.moved then
    dataDirty = true
  end

  dragState = nil
  markDirty("body")
end

handleCanvasMouseScroll = function(dir, x, y)
  if #canvasBlocks == 0 then return end
  if selectedBlockIndex == 0 then selectedBlockIndex = 1 end
  selectedBlockIndex = ((selectedBlockIndex - 1 + dir) % #canvasBlocks) + 1
  markDirty("body")
end

-- ======================================================================
-- GLOBAL EVENT DISPATCH (mode switching, quitting)
-- ======================================================================
actionQuit = function()
  running = false
end

toggleViewMode = function()
  appMode = (appMode == "list") and "canvas" or "list"
  markDirty("all")
  setStatus(appMode == "canvas" and "Canvas view - drag blocks to arrange, press N to add one." or "List view.", colors.lightBlue)
end

handleGlobalKey = function(key, isHeld)
  if key == keys.v and not isHeld then
    toggleViewMode()
    return
  end
  if key == keys.q and not isHeld then
    actionQuit()
    return
  end
  if appMode == "list" then
    handleKey(key, isHeld)
  else
    handleCanvasKey(key, isHeld)
  end
end

-- ======================================================================
-- POLLING (bridge inputs) - links referenced by on-screen rows/blocks are
-- polled every tick, others round-robin so hundreds of links stay
-- responsive. Comparisons use the entry table itself (not its array
-- index) so a mid-poll deletion, sort, or duplicate can never mix up
-- which link a result belongs to. This runs entirely inside pollLoop,
-- its own coroutine, so a slow or unresponsive bridge can never delay
-- input handling.
-- ======================================================================
collectPriorityEntries = function()
  local set = {}
  if appMode == "list" then
    for row = 0, LIST_HEIGHT - 1 do
      local drow = displayRows[scrollOffset + row + 1]
      if drow then
        local entry = links[drow.linkIndex]
        if entry then set[entry] = true end
      end
    end
  else
    for _, block in ipairs(canvasBlocks) do
      if block.linkId then
        local entry = findLinkEntryById(block.linkId)
        if entry then set[entry] = true end
      end
    end
  end
  return set
end

local function pollEntryInputs(entry)
  local changed = false
  if entry.kind == KIND_SINGLE then
    if entry.mode == MODE_INPUT then
      local val = safeGetSignal(entry.freq1, entry.freq2)
      if val and val ~= entry.input then entry.input = val; changed = true end
    end
  else
    local sVal = safeGetSignal(entry.status.freq1, entry.status.freq2)
    if sVal and sVal ~= entry.status.input then entry.status.input = sVal; changed = true end
  end
  return changed
end

pollVisible = function()
  local priority = collectPriorityEntries()
  local changed = false
  for _, entry in ipairs(links) do
    if priority[entry] and pollEntryInputs(entry) then changed = true end
  end
  if changed then markDirty("body") end
end

pollBackground = function()
  local total = #links
  if total == 0 then return end
  local priority = collectPriorityEntries()
  local changed = false
  local count = 0
  while count < BG_POLL_PER_TICK and count < total do
    local idx = bgPollIndex
    local entry = links[idx]
    if entry and not priority[entry] then
      if pollEntryInputs(entry) then changed = true end
    end
    bgPollIndex = bgPollIndex + 1
    if bgPollIndex > total then bgPollIndex = 1 end
    count = count + 1
  end
  if changed then markDirty("body") end
end

-- ======================================================================
-- MAIN LOOP
-- Three independent loops run together via parallel.waitForAny. Because
-- events are broadcast to every waiting branch, each loop simply ignores
-- events it doesn't care about (e.g. pollLoop only reacts to its own
-- timer ID). As soon as inputLoop returns (on Quit), the other two are
-- torn down automatically.
-- ======================================================================
inputLoop = function()
  while true do
    local ev, p1, p2, p3 = os.pullEvent()

    if ev == "key" then
      if p1 == keys.leftShift or p1 == keys.rightShift then isShiftDown = true end
      handleGlobalKey(p1, p2)

    elseif ev == "key_up" then
      if p1 == keys.leftShift or p1 == keys.rightShift then isShiftDown = false end

    elseif ev == "char" then
      if appMode == "list" then handleChar(p1) end

    elseif ev == "mouse_click" then
      if appMode == "list" then handleMouseClick(p1, p2, p3) else handleCanvasMouseClick(p1, p2, p3) end

    elseif ev == "mouse_drag" then
      if appMode == "canvas" then handleCanvasMouseDrag(p1, p2, p3) end

    elseif ev == "mouse_up" then
      if appMode == "canvas" then handleCanvasMouseUp(p1, p2, p3) end

    elseif ev == "mouse_scroll" then
      if appMode == "list" then handleMouseScroll(p1, p2, p3) else handleCanvasMouseScroll(p1, p2, p3) end

    elseif ev == "term_resize" then
      W, H = term.getSize()
      LIST_BOTTOM = H - FOOTER_HEIGHT
      LIST_HEIGHT = math.max(1, LIST_BOTTOM - LIST_TOP + 1)
      ensureVisible()
      clampAllBlocksToScreen()
      term.setBackgroundColor(colors.black)
      term.clear()
      markDirty("all")
    end

    if not running then return end
  end
end

pollLoop = function()
  local pollTimerId = os.startTimer(POLL_TICK)
  local lastConnected = bridgeConn.connected
  while true do
    local ev, id = os.pullEvent("timer")
    if id == pollTimerId then
      checkBridgeConnection()
      pollVisible()
      pollBackground()

      if bridgeConn.connected ~= lastConnected then
        lastConnected = bridgeConn.connected
        markDirty("header")
        markDirty("footer")
      end

      if statusMsg ~= "" and os.clock() > statusExpireAt then
        statusMsg = ""
        markDirty("footer")
      end

      if dataDirty then
        saveData()
        dataDirty = false
      end

      pollTimerId = os.startTimer(POLL_TICK)
    end
    if not running then return end
  end
end

renderLoop = function()
  local renderTimerId = os.startTimer(RENDER_TICK)
  while true do
    local ev, id = os.pullEvent("timer")
    if id == renderTimerId then
      if not suspendRender then redraw() end
      renderTimerId = os.startTimer(RENDER_TICK)
    end
    if not running then return end
  end
end

main = function()
  loadData()
  refreshDisplayRows()
  clampAllBlocksToScreen()

  term.setBackgroundColor(colors.black)
  term.setTextColor(colors.white)
  term.clear()
  term.setCursorBlink(false)

  markDirty("all")
  redraw() -- paint the very first frame immediately, don't wait on the render loop

  parallel.waitForAny(inputLoop, pollLoop, renderLoop)

  saveData()
  term.setBackgroundColor(colors.black)
  term.setTextColor(colors.white)
  term.clear()
  term.setCursorPos(1, 1)
  print("Redstone Link Controller closed. Data saved to " .. SAVE_FILE)
end

-- ======================================================================
-- ENTRY POINT (wrapped so unexpected errors still save data first)
-- ======================================================================
local ok, err = pcall(main)
if not ok then
  pcall(saveData)
  term.setBackgroundColor(colors.black)
  term.setTextColor(colors.red)
  print("Redstone Link Controller encountered an error:")
  print(tostring(err))
  print("Your link data has been saved where possible.")
end