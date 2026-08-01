-- ============================================================================
-- Redstone Link Controller for CC:Tweaked
-- Controls Create Redstone Links via PeripheralWorks redstone_link_bridge
-- ============================================================================

local bridge = peripheral.find("redstone_link_bridge")
assert(bridge, "No redstone_link_bridge found")

-- ============================================================================
-- Configuration
-- ============================================================================

local CONFIG = {
    SAVE_FILE = "redstone_links.dat",
    POLL_RATE = 100,  -- milliseconds between polls
    MAX_DISPLAY = 20,  -- max links shown on screen
    HEADER_HEIGHT = 2,
    FOOTER_HEIGHT = 1,
}

-- ============================================================================
-- Color Scheme
-- ============================================================================

local COLORS_SCHEME = {
    HEADER_BG = colors.blue,
    HEADER_FG = colors.white,
    NORMAL_FG = colors.white,
    NORMAL_BG = colors.black,
    SELECTED_BG = colors.cyan,
    SELECTED_FG = colors.black,
    FOOTER_BG = colors.gray,
    FOOTER_FG = colors.white,
    ERROR_FG = colors.red,
    SUCCESS_FG = colors.lime,
    INFO_FG = colors.yellow,
}

-- ============================================================================
-- Data Storage
-- ============================================================================

local links = {}
local selectedIndex = 1
local scrollOffset = 0
local searchFilter = ""
local sortAlpha = true
local lastPollTime = 0
local lastDrawTime = 0
local running = true

-- ============================================================================
-- Utility Functions
-- ============================================================================

local function save()
    local f = io.open(CONFIG.SAVE_FILE, "w")
    if f then
        f:write(textutils.serialize(links))
        f:close()
    end
end

local function load()
    local f = io.open(CONFIG.SAVE_FILE, "r")
    if f then
        local data = f:read("*a")
        f:close()
        if data and #data > 0 then
            links = textutils.unserialize(data) or {}
        end
    end
    return links
end

local function getFilteredLinks()
    local filtered = {}
    for _, link in ipairs(links) do
        if searchFilter == "" or
           string.find(link.name:lower(), searchFilter:lower(), 1, true) then
            table.insert(filtered, link)
        end
    end
    
    if sortAlpha then
        table.sort(filtered, function(a, b)
            return a.name:lower() < b.name:lower()
        end)
    end
    
    return filtered
end

local function findLinkByName(name)
    for i, link in ipairs(links) do
        if link.name == name then
            return link, i
        end
    end
    return nil, nil
end

local function pollLinkSignals()
    for _, link in ipairs(links) do
        local signal = bridge.getLinkSignal(link.freq1, link.freq2)
        link.input = signal or 0
    end
end

local function sendLinkSignal(link)
    bridge.sendLinkSignal(link.freq1, link.freq2, link.output or 0)
end

-- ============================================================================
-- Input Functions
-- ============================================================================

local function readInput(prompt, validator)
    term.setCursorBlink(true)
    while true do
        term.setTextColor(COLORS_SCHEME.INFO_FG)
        term.write(prompt)
        term.setTextColor(COLORS_SCHEME.NORMAL_FG)
        
        local input = read()
        term.setTextColor(COLORS_SCHEME.NORMAL_FG)
        term.clearLine()
        
        if validator then
            local valid, message = validator(input)
            if not valid then
                term.setTextColor(COLORS_SCHEME.ERROR_FG)
                term.write(message)
                term.setTextColor(COLORS_SCHEME.NORMAL_FG)
                print()
                term.write("Press Enter to try again...")
                read()
                term.clearLine()
            else
                term.setCursorBlink(false)
                return input
            end
        else
            term.setCursorBlink(false)
            return input
        end
    end
end

local function validateFrequency(freq)
    if freq == "" then
        return false, "Frequency cannot be empty"
    end
    local num = tonumber(freq)
    if not num then
        return false, "Frequency must be a number"
    end
    if num < 0 or num > 65535 then
        return false, "Frequency must be 0-65535"
    end
    return true, nil
end

local function validateName(name)
    if name == "" then
        return false, "Name cannot be empty"
    end
    return true, nil
end

local function addLink()
    term.clear()
    term.setCursorPos(1, 1)
    
    term.setTextColor(COLORS_SCHEME.HEADER_FG)
    term.write("Add New Link")
    term.setTextColor(COLORS_SCHEME.NORMAL_FG)
    print()
    print()
    
    local name = readInput("Name: ", validateName)
    print()
    
    local freq1 = readInput("Frequency 1: ", validateFrequency)
    print()
    
    local freq2 = readInput("Frequency 2: ", validateFrequency)
    print()
    
    table.insert(links, {
        name = name,
        freq1 = tonumber(freq1),
        freq2 = tonumber(freq2),
        input = 0,
        output = 0,
    })
    
    save()
    selectedIndex = #links
    searchFilter = ""
    
    term.setTextColor(COLORS_SCHEME.SUCCESS_FG)
    term.write("Link added!")
    term.setTextColor(COLORS_SCHEME.NORMAL_FG)
    sleep(0.5)
end

local function editLink(link)
    term.clear()
    term.setCursorPos(1, 1)
    
    term.setTextColor(COLORS_SCHEME.HEADER_FG)
    term.write("Edit Link: " .. link.name)
    term.setTextColor(COLORS_SCHEME.NORMAL_FG)
    print()
    print()
    
    local newName = readInput("Name (" .. link.name .. "): ", function(input)
        if input == "" then return true end
        return validateName(input)
    end)
    if newName == "" then newName = link.name end
    print()
    
    local newFreq1 = readInput("Frequency 1 (" .. link.freq1 .. "): ", function(input)
        if input == "" then return true end
        return validateFrequency(input)
    end)
    if newFreq1 ~= "" then link.freq1 = tonumber(newFreq1) end
    print()
    
    local newFreq2 = readInput("Frequency 2 (" .. link.freq2 .. "): ", function(input)
        if input == "" then return true end
        return validateFrequency(input)
    end)
    if newFreq2 ~= "" then link.freq2 = tonumber(newFreq2) end
    print()
    
    link.name = newName
    save()
    
    term.setTextColor(COLORS_SCHEME.SUCCESS_FG)
    term.write("Link updated!")
    term.setTextColor(COLORS_SCHEME.NORMAL_FG)
    sleep(0.5)
end

local function deleteLink(index)
    table.remove(links, index)
    save()
    if selectedIndex > #links then
        selectedIndex = math.max(1, #links)
    end
end

local function renameLink(index, link)
    term.clear()
    term.setCursorPos(1, 1)
    
    term.setTextColor(COLORS_SCHEME.HEADER_FG)
    term.write("Rename Link")
    term.setTextColor(COLORS_SCHEME.NORMAL_FG)
    print()
    print()
    
    local newName = readInput("New name (" .. link.name .. "): ", function(input)
        if input == "" then return true end
        return validateName(input)
    end)
    
    if newName ~= "" then
        link.name = newName
        save()
    end
    
    term.setTextColor(COLORS_SCHEME.SUCCESS_FG)
    term.write("Link renamed!")
    term.setTextColor(COLORS_SCHEME.NORMAL_FG)
    sleep(0.5)
end

local function duplicateLink(index, link)
    local newLink = {
        name = link.name .. " (copy)",
        freq1 = link.freq1,
        freq2 = link.freq2,
        input = link.input,
        output = 0,
    }
    table.insert(links, newLink)
    save()
    selectedIndex = #links
    
    term.setTextColor(COLORS_SCHEME.SUCCESS_FG)
    term.write("Link duplicated!")
    term.setTextColor(COLORS_SCHEME.NORMAL_FG)
    sleep(0.5)
end

-- ============================================================================
-- UI Drawing Functions
-- ============================================================================

local function drawHeader()
    term.setCursorPos(1, 1)
    term.setBackgroundColor(COLORS_SCHEME.HEADER_BG)
    term.setTextColor(COLORS_SCHEME.HEADER_FG)
    
    local width = term.getSize()
    local header = " Redstone Link Controller "
    local padding = math.floor((width - #header) / 2)
    
    term.clearLine()
    term.write(string.rep(" ", padding) .. header)
    
    term.setCursorPos(1, 2)
    term.clearLine()
    
    term.setBackgroundColor(COLORS_SCHEME.NORMAL_BG)
    term.setTextColor(COLORS_SCHEME.NORMAL_FG)
end

local function drawFooter()
    local width, height = term.getSize()
    term.setCursorPos(1, height)
    term.setBackgroundColor(COLORS_SCHEME.FOOTER_BG)
    term.setTextColor(COLORS_SCHEME.FOOTER_FG)
    term.clearLine()
    
    local footer = "A:Add D:Del R:Rename E:Edit SPC:Toggle ↑↓:+-Out Search Q:Exit"
    term.write(footer:sub(1, width))
    
    term.setBackgroundColor(COLORS_SCHEME.NORMAL_BG)
    term.setTextColor(COLORS_SCHEME.NORMAL_FG)
end

local function drawLinkRow(y, link, selected)
    local width, _ = term.getSize()
    
    if selected then
        term.setBackgroundColor(COLORS_SCHEME.SELECTED_BG)
        term.setTextColor(COLORS_SCHEME.SELECTED_FG)
    else
        term.setBackgroundColor(COLORS_SCHEME.NORMAL_BG)
        term.setTextColor(COLORS_SCHEME.NORMAL_FG)
    end
    
    term.setCursorPos(1, y)
    term.clearLine()
    
    local input = link.input or 0
    local output = link.output or 0
    
    local text = string.format(" %-20s [F1:%5d F2:%5d] IN:%-2d OUT:%-2d",
        link.name:sub(1, 20),
        link.freq1,
        link.freq2,
        input,
        output
    )
    
    if #text > width then
        text = text:sub(1, width)
    end
    
    term.write(text)
    term.write(string.rep(" ", width - #text))
end

local function drawLinkList()
    local width, height = term.getSize()
    local contentHeight = height - CONFIG.HEADER_HEIGHT - CONFIG.FOOTER_HEIGHT
    
    local filtered = getFilteredLinks()
    
    -- Adjust scroll offset
    if selectedIndex > #filtered then
        selectedIndex = math.max(1, #filtered)
    end
    
    if selectedIndex - scrollOffset > contentHeight then
        scrollOffset = selectedIndex - contentHeight
    elseif selectedIndex - scrollOffset < 1 then
        scrollOffset = selectedIndex - 1
    end
    
    -- Draw links
    for i = 1, contentHeight do
        local linkIndex = scrollOffset + i
        local y = CONFIG.HEADER_HEIGHT + i
        
        if linkIndex <= #filtered then
            local link = filtered[linkIndex]
            local selected = (linkIndex == selectedIndex)
            drawLinkRow(y, link, selected)
        else
            term.setCursorPos(1, y)
            term.setBackgroundColor(COLORS_SCHEME.NORMAL_BG)
            term.setTextColor(COLORS_SCHEME.NORMAL_FG)
            term.clearLine()
        end
    end
end

local function drawUI()
    drawHeader()
    drawLinkList()
    drawFooter()
    term.setCursorPos(1, CONFIG.HEADER_HEIGHT + 1)
end

-- ============================================================================
-- Event Handling
-- ============================================================================

local function handleKeyPress(key)
    local filtered = getFilteredLinks()
    
    if key == "up" then
        selectedIndex = math.max(1, selectedIndex - 1)
    elseif key == "down" then
        selectedIndex = math.min(#filtered, selectedIndex + 1)
    elseif key == "a" then
        addLink()
        filtered = getFilteredLinks()
    elseif key == "d" then
        if #filtered > 0 then
            local link = filtered[selectedIndex]
            local _, realIndex = findLinkByName(link.name)
            if realIndex then
                deleteLink(realIndex)
            end
        end
    elseif key == "r" then
        if #filtered > 0 then
            local link = filtered[selectedIndex]
            local _, realIndex = findLinkByName(link.name)
            if realIndex then
                renameLink(realIndex, link)
            end
        end
    elseif key == "e" then
        if #filtered > 0 then
            local link = filtered[selectedIndex]
            local _, realIndex = findLinkByName(link.name)
            if realIndex then
                editLink(link)
            end
        end
    elseif key == "space" then
        if #filtered > 0 then
            local link = filtered[selectedIndex]
            link.output = (link.output == 0) and 15 or 0
            sendLinkSignal(link)
            save()
        end
    elseif key == "up" or key == "+" or key == "=" then
        if #filtered > 0 then
            local link = filtered[selectedIndex]
            link.output = math.min(15, (link.output or 0) + 1)
            sendLinkSignal(link)
            save()
        end
    elseif key == "down" or key == "-" or key == "_" then
        if #filtered > 0 then
            local link = filtered[selectedIndex]
            link.output = math.max(0, (link.output or 0) - 1)
            sendLinkSignal(link)
            save()
        end
    elseif key == "return" then
        if #filtered > 0 then
            local link = filtered[selectedIndex]
            local _, realIndex = findLinkByName(link.name)
            if realIndex then
                editLink(link)
            end
        end
    elseif key == "tab" then
        -- Show search prompt
        term.clear()
        term.setCursorPos(1, 1)
        term.setTextColor(COLORS_SCHEME.INFO_FG)
        term.write("Search: ")
        term.setTextColor(COLORS_SCHEME.NORMAL_FG)
        term.setCursorBlink(true)
        searchFilter = read()
        term.setCursorBlink(false)
        selectedIndex = 1
        scrollOffset = 0
    elseif key == "c" then
        if #filtered > 0 then
            local link = filtered[selectedIndex]
            local _, realIndex = findLinkByName(link.name)
            if realIndex then
                duplicateLink(realIndex, link)
            end
        end
    elseif key == "q" then
        running = false
    end
end

local function handleMouseClick(x, y)
    local width, height = term.getSize()
    
    if y < CONFIG.HEADER_HEIGHT or y > height - CONFIG.FOOTER_HEIGHT then
        return
    end
    
    local filtered = getFilteredLinks()
    local clickIndex = scrollOffset + (y - CONFIG.HEADER_HEIGHT)
    
    if clickIndex >= 1 and clickIndex <= #filtered then
        selectedIndex = clickIndex
    end
end

-- ============================================================================
-- Main Loop
-- ============================================================================

local function main()
    load()
    
    -- Handle bridge disconnect
    local function bridgeConnected()
        return peripheral.find("redstone_link_bridge") ~= nil
    end
    
    while running do
        -- Poll signals
        if bridgeConnected() then
            pollLinkSignals()
        else
            term.clear()
            term.setCursorPos(1, 1)
            term.setTextColor(COLORS_SCHEME.ERROR_FG)
            term.write("ERROR: redstone_link_bridge not found!")
            term.setTextColor(COLORS_SCHEME.NORMAL_FG)
            print()
            term.write("Waiting for reconnection...")
            
            -- Wait for reconnection
            while not bridgeConnected() and running do
                sleep(1)
            end
            
            if running then
                bridge = peripheral.find("redstone_link_bridge")
            end
            continue
        end
        
        -- Draw UI
        drawUI()
        
        -- Handle input (non-blocking)
        local event, arg1, arg2, arg3 = os.pullEvent(1)
        
        if event == "key" then
            handleKeyPress(keys.getName(arg1))
        elseif event == "mouse_click" then
            handleMouseClick(arg2, arg3)
        end
    end
    
    term.clear()
    term.setCursorPos(1, 1)
    term.setTextColor(colors.white)
    term.setBackgroundColor(colors.black)
    print("Redstone Link Controller closed.")
end

main()
