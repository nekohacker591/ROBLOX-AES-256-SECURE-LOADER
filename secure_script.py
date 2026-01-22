import sys
import base64
import os
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad
from Crypto.Hash import SHA256
from Crypto.Random import get_random_bytes

# -----------------------------------------------------------------------------
# LUA TEMPLATE
# Changes: NEKO'S AES-256 SECURE LOADER
# -----------------------------------------------------------------------------
LUA_TEMPLATE = r"""
--[[ 
   NEKO'S AES-256 SECURE LOADER
]]

local ENCRYPTED_DATA = "{ENCRYPTED_PAYLOAD}"
local IV_DATA = "{IV_PAYLOAD}"

local CoreGui = game:GetService("CoreGui")
local Players = game:GetService("Players")
local RunService = game:GetService("RunService")
local TweenService = game:GetService("TweenService")
local SoundService = game:GetService("SoundService")

local function SecureRunner()
    local Lib = {}
    
    --#region CRYPTO
    local bit = bit32
    local bxor, band, rshift, lshift, bnot, bor = bit.bxor, bit.band, bit.rshift, bit.lshift, bit.bnot, bit.bor
    local floor, char, byte, sub = math.floor, string.char, string.byte, string.sub
    local table_insert, table_concat = table.insert, table.concat
    local clock = os.clock

    local b64chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'
    local b64map = {}
    for i = 1, 64 do b64map[sub(b64chars, i, i)] = i - 1 end

    function Lib.b64_decode(data)
        data = string.gsub(data, '[^'..b64chars..'=]', '')
        local len = #data
        if len % 4 ~= 0 then error("B64 Error") end
        local padding = 0; if sub(data, -2) == '==' then padding = 2 elseif sub(data, -1) == '=' then padding = 1 end
        local t = {}
        for i = 1, len, 4 do
            local a, b, c, d = byte(data, i, i+3)
            local v = lshift(b64map[char(a)], 18) + lshift(b64map[char(b)], 12) + lshift(b64map[char(c) or 61] or 0, 6) + (b64map[char(d) or 61] or 0)
            table_insert(t, char(band(rshift(v, 16), 0xFF)))
            if i < len - 3 or padding < 2 then table_insert(t, char(band(rshift(v, 8), 0xFF))) end
            if i < len - 3 or padding < 1 then table_insert(t, char(band(v, 0xFF))) end
        end
        return table_concat(t)
    end

    function Lib.sha256(str)
        local K = {0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2}
        local function rrot(x, n) return bor(rshift(x, n), lshift(x, 32 - n)) end
        local h = {0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19}
        local function toBytes(n) return char(band(rshift(n, 24), 0xFF), band(rshift(n, 16), 0xFF), band(rshift(n, 8), 0xFF), band(n, 0xFF)) end
        local len = #str * 8; str = str .. "\128"; local k = (56 - #str) % 64; str = str .. string.rep("\0", k) .. toBytes(0) .. toBytes(len)
        for i = 1, #str, 64 do
            local w = {}; local chunk = sub(str, i, i+63)
            for j = 0, 15 do w[j] = bor(lshift(byte(chunk, j*4+1), 24), lshift(byte(chunk, j*4+2), 16), lshift(byte(chunk, j*4+3), 8), byte(chunk, j*4+4)) end
            for j = 16, 63 do local s0 = bxor(rrot(w[j-15], 7), rrot(w[j-15], 18), rshift(w[j-15], 3)); local s1 = bxor(rrot(w[j-2], 17), rrot(w[j-2], 19), rshift(w[j-2], 10)); w[j] = (w[j-16] + s0 + w[j-7] + s1) % 4294967296 end
            local a,b,c,d,e,f,g,h_temp = h[1],h[2],h[3],h[4],h[5],h[6],h[7],h[8]
            for j = 0, 63 do local S1 = bxor(rrot(e, 6), rrot(e, 11), rrot(e, 25)); local ch = bxor(band(e, f), band(bnot(e), g)); local temp1 = (h_temp + S1 + ch + K[j+1] + w[j]) % 4294967296; local S0 = bxor(rrot(a, 2), rrot(a, 13), rrot(a, 22)); local maj = bxor(band(a, b), band(a, c), band(b, c)); local temp2 = (S0 + maj) % 4294967296; h_temp, g, f, e, d, c, b, a = g, f, e, (d + temp1) % 4294967296, c, b, a, (temp1 + temp2) % 4294967296 end
            h[1]=(h[1]+a)%4294967296; h[2]=(h[2]+b)%4294967296; h[3]=(h[3]+c)%4294967296; h[4]=(h[4]+d)%4294967296; h[5]=(h[5]+e)%4294967296; h[6]=(h[6]+f)%4294967296; h[7]=(h[7]+g)%4294967296; h[8]=(h[8]+h_temp)%4294967296
        end
        return toBytes(h[1])..toBytes(h[2])..toBytes(h[3])..toBytes(h[4])..toBytes(h[5])..toBytes(h[6])..toBytes(h[7])..toBytes(h[8])
    end

    Lib.AES = {}
    local SBox = {0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16}
    local InvSBox = {} for i = 1, #SBox do InvSBox[SBox[i]+1] = i-1 end
    local Rcon = {0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36}
    
    local function SubBytes(state) for i = 1, #state do state[i] = SBox[state[i] + 1] end end
    local function InvSubBytes(state) for i = 1, #state do state[i] = InvSBox[state[i] + 1] end end
    local function AddRoundKey(state, keySchedule, round) local offset = round * 16; for i = 1, 16 do local k = keySchedule[offset + i]; if not k then error("KeyErr") end; state[i] = bxor(state[i], k) end end
    local function InvShiftRows(s) local t = {s[1],s[14],s[11],s[8],s[5],s[2],s[15],s[12],s[9],s[6],s[3],s[16],s[13],s[10],s[7],s[4]}; for i=1,16 do s[i]=t[i] end end
    local function gmul(a, b) local p = 0; for i = 1, 8 do if band(b, 1) == 1 then p = bxor(p, a) end; local hi = band(a, 0x80); a = band(lshift(a, 1), 0xFF); if hi == 0x80 then a = bxor(a, 0x1b) end; b = rshift(b, 1) end; return p end
    local function InvMixColumns(s) local t = {unpack(s)}; for c = 0, 3 do local off = c * 4; s[off+1] = bxor(gmul(0x0e, t[off+1]), gmul(0x0b, t[off+2]), gmul(0x0d, t[off+3]), gmul(0x09, t[off+4])); s[off+2] = bxor(gmul(0x09, t[off+1]), gmul(0x0e, t[off+2]), gmul(0x0b, t[off+3]), gmul(0x0d, t[off+4])); s[off+3] = bxor(gmul(0x0d, t[off+1]), gmul(0x09, t[off+2]), gmul(0x0e, t[off+3]), gmul(0x0b, t[off+4])); s[off+4] = bxor(gmul(0x0b, t[off+1]), gmul(0x0d, t[off+2]), gmul(0x09, t[off+3]), gmul(0x0e, t[off+4])) end end
    
    local function ExpandKey(keyBytes)
        local w = {}; for i = 1, 32 do w[i] = keyBytes[i] end; local i, words = 32, 8
        while words < 60 do
            local temp = {w[i-3], w[i-2], w[i-1], w[i]}
            if words % 8 == 0 then local t = temp[1]; temp[1], temp[2], temp[3], temp[4] = temp[2], temp[3], temp[4], t; for j=1,4 do temp[j] = SBox[temp[j]+1] end; temp[1] = bxor(temp[1], Rcon[floor(words/8)])
            elseif words % 8 == 4 then for j=1,4 do temp[j] = SBox[temp[j]+1] end end
            for j=1,4 do w[i+j] = bxor(w[i-32+j], temp[j]) end
            i = i + 4; words = words + 1
        end
        return w
    end
    
    function Lib.Decrypt(encrypted, keyStr, ivStr, progressCallback)
        if #encrypted % 16 ~= 0 then error("CipherLen") end
        local keyBytes = {byte(keyStr, 1, 32)}
        local ivBytes = {byte(ivStr, 1, 16)}
        local expandedKey = ExpandKey(keyBytes)
        local out = {}
        local prevBlock = ivBytes
        
        local totalBytes = #encrypted
        local processedCount = 0
        local lastYieldTime = clock()
        
        for i = 1, totalBytes, 16 do
            local block = {byte(encrypted, i, i+15)}
            if #block < 16 then error("BlockErr") end
            local state = {unpack(block)}
            
            AddRoundKey(state, expandedKey, 14)
            for round = 13, 1, -1 do InvShiftRows(state); InvSubBytes(state); AddRoundKey(state, expandedKey, round); InvMixColumns(state) end
            InvShiftRows(state); InvSubBytes(state); AddRoundKey(state, expandedKey, 0)
            
            for j = 1, 16 do table_insert(out, char(bxor(state[j], prevBlock[j]))) end
            prevBlock = block
            processedCount = processedCount + 16
            
            if clock() - lastYieldTime > 0.015 then 
                if progressCallback then progressCallback(processedCount / totalBytes) end
                task.wait()
                lastYieldTime = clock()
            end
        end
        return table_concat(out)
    end
    
    function Lib.Unpad(str)
        local len = #str; if len == 0 then return str end; local p = byte(str, len)
        if p > 0 and p <= 16 then for i = 1, p do if byte(str, len - i + 1) ~= p then return str end end; return sub(str, 1, len - p) end
        return str
    end
    --#endregion

    --#region UI SETUP
    local Screen = Instance.new("ScreenGui")
    Screen.Name = "SecureLoader"
    Screen.ResetOnSpawn = false
    Screen.IgnoreGuiInset = true
    Screen.DisplayOrder = 999
    
    local Sounds = {
        Spawn = Instance.new("Sound"), 
        Click = Instance.new("Sound"),
        Hover = Instance.new("Sound"),
        Success = Instance.new("Sound"),
        Fail = Instance.new("Sound")
    }
    Sounds.Spawn.SoundId = "rbxassetid://3320590485"; Sounds.Spawn.Volume = 3.5
    Sounds.Click.SoundId = "rbxassetid://6042053626"; Sounds.Click.Volume = 3
    Sounds.Hover.SoundId = "rbxassetid://6895079853"; Sounds.Hover.PlaybackSpeed = 1.5; Sounds.Hover.Volume = 1
    Sounds.Success.SoundId = "rbxassetid://101176804827210"; Sounds.Success.Volume = 3
    Sounds.Fail.SoundId = "rbxassetid://87519554692663"; Sounds.Fail.Volume = 3
    for _, s in pairs(Sounds) do s.Parent = Screen end

    local function ScrambleText(obj, targetText, duration)
        local chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!@#$%^&*"
        local t = 0
        while t < duration do
            local str = ""
            for i = 1, #targetText do
                if math.random() > (t/duration) then
                    str = str .. string.sub(chars, math.random(1, #chars), math.random(1, #chars))
                else
                    str = str .. string.sub(targetText, i, i)
                end
            end
            obj.Text = str
            t = t + RunService.Heartbeat:Wait()
        end
        obj.Text = targetText
    end

    -- Main Container (SOLID)
    local Main = Instance.new("Frame")
    Main.Size = UDim2.new(0, 360, 0, 200)
    -- Start slightly lower for slide-up effect
    Main.Position = UDim2.new(0.5, -180, 0.5, -80) 
    Main.BackgroundColor3 = Color3.fromRGB(15, 15, 17)
    Main.BackgroundTransparency = 1 -- Start Invisible
    Main.BorderSizePixel = 0
    Main.Active = true
    Main.Draggable = true
    Main.Parent = Screen
    Main.ClipsDescendants = true
    
    local MainCorner = Instance.new("UICorner") MainCorner.CornerRadius = UDim.new(0, 12) MainCorner.Parent = Main
    local MainStroke = Instance.new("UIStroke") MainStroke.Color = Color3.fromRGB(60, 60, 70) MainStroke.Thickness = 1 MainStroke.Transparency = 0.6 MainStroke.Parent = Main
    
    

    local Header = Instance.new("TextLabel")
    Header.Text = "SECURE GATEWAY" -- Static Text (No scramble)
    Header.Size = UDim2.new(1, -40, 0, 50)
    Header.Position = UDim2.new(0, 20, 0, 0)
    Header.BackgroundTransparency = 1
    Header.TextColor3 = Color3.fromRGB(240, 240, 240)
    Header.Font = Enum.Font.GothamBold
    Header.TextSize = 14
    Header.TextXAlignment = Enum.TextXAlignment.Left
    Header.Parent = Main
    
    local Ver = Instance.new("TextLabel")
    Ver.Text = "AES-256"
    Ver.Size = UDim2.new(0, 50, 0, 50)
    Ver.Position = UDim2.new(1, -60, 0, 0)
    Ver.BackgroundTransparency = 1
    Ver.TextColor3 = Color3.fromRGB(80, 80, 90)
    Ver.Font = Enum.Font.Code
    Ver.TextSize = 11
    Ver.TextXAlignment = Enum.TextXAlignment.Right
    Ver.Parent = Main

    local InputFrame = Instance.new("Frame")
    InputFrame.Size = UDim2.new(0.9, 0, 0, 45)
    InputFrame.Position = UDim2.new(0.05, 0, 0, 60)
    InputFrame.BackgroundColor3 = Color3.fromRGB(10, 10, 12)
    InputFrame.BorderSizePixel = 0
    InputFrame.Parent = Main
    local InputCorner = Instance.new("UICorner") InputCorner.CornerRadius = UDim.new(0, 8) InputCorner.Parent = InputFrame
    local InputStroke = Instance.new("UIStroke") InputStroke.Color = Color3.fromRGB(40, 40, 45) InputStroke.Thickness = 1 InputStroke.Parent = InputFrame
    
    local InputBox = Instance.new("TextBox")
    InputBox.Size = UDim2.new(1, -20, 1, 0)
    InputBox.Position = UDim2.new(0, 10, 0, 0)
    InputBox.BackgroundTransparency = 1
    InputBox.TextColor3 = Color3.fromRGB(255, 255, 255)
    InputBox.PlaceholderColor3 = Color3.fromRGB(100, 100, 110)
    InputBox.PlaceholderText = "Enter Decryption Key"
    InputBox.Text = "" 
    InputBox.Font = Enum.Font.GothamMedium
    InputBox.TextSize = 14
    InputBox.TextXAlignment = Enum.TextXAlignment.Left
    InputBox.ClearTextOnFocus = false
    InputBox.Parent = InputFrame
    
    local ProgressBg = Instance.new("Frame")
    ProgressBg.Size = UDim2.new(0.9, 0, 0, 2)
    ProgressBg.Position = UDim2.new(0.05, 0, 0, 120)
    ProgressBg.BackgroundColor3 = Color3.fromRGB(30, 30, 35)
    ProgressBg.BorderSizePixel = 0
    ProgressBg.Parent = Main
    
    local ProgressFill = Instance.new("Frame")
    ProgressFill.Size = UDim2.new(0, 0, 1, 0)
    ProgressFill.BackgroundColor3 = Color3.fromRGB(0, 255, 255)
    ProgressFill.BorderSizePixel = 0
    ProgressFill.Parent = ProgressBg
    
    local StatusTxt = Instance.new("TextLabel")
    StatusTxt.Text = "SYSTEM READY"
    StatusTxt.Size = UDim2.new(0.9, 0, 0, 20)
    StatusTxt.Position = UDim2.new(0.05, 0, 0, 125)
    StatusTxt.BackgroundTransparency = 1
    StatusTxt.TextColor3 = Color3.fromRGB(100, 100, 110)
    StatusTxt.Font = Enum.Font.Code
    StatusTxt.TextSize = 11
    StatusTxt.TextXAlignment = Enum.TextXAlignment.Right
    StatusTxt.Parent = Main

    local Btn = Instance.new("TextButton")
    Btn.Size = UDim2.new(0.9, 0, 0, 40)
    Btn.Position = UDim2.new(0.05, 0, 1, -50)
    Btn.BackgroundColor3 = Color3.fromRGB(0, 120, 220)
    Btn.Text = ""
    Btn.AutoButtonColor = false
    Btn.Parent = Main
    local BtnCorner = Instance.new("UICorner") BtnCorner.CornerRadius = UDim.new(0, 8) BtnCorner.Parent = Btn
    
    local BtnLabel = Instance.new("TextLabel")
    BtnLabel.Text = "INITIALIZE DECRYPTION"
    BtnLabel.Size = UDim2.new(1,0,1,0)
    BtnLabel.BackgroundTransparency = 1
    BtnLabel.TextColor3 = Color3.fromRGB(255,255,255)
    BtnLabel.Font = Enum.Font.GothamBold
    BtnLabel.TextSize = 12
    BtnLabel.Parent = Btn

    -- ANIMATIONS
    local function Intro()
        Sounds.Spawn:Play()
        
        -- Slide Up & Fade In
        -- Tweening to final position and 0 transparency
        TweenService:Create(Main, TweenInfo.new(0.6, Enum.EasingStyle.Quart, Enum.EasingDirection.Out), {
            Position = UDim2.new(0.5, -180, 0.5, -100), -- Final Center
            BackgroundTransparency = 0 -- Fully Visible
        }):Play()
        
        
    end
    
    InputBox.Focused:Connect(function()
        TweenService:Create(InputStroke, TweenInfo.new(0.3), {Color = Color3.fromRGB(0, 180, 255), Transparency = 0}):Play()
    end)
    InputBox.FocusLost:Connect(function()
        TweenService:Create(InputStroke, TweenInfo.new(0.3), {Color = Color3.fromRGB(40, 40, 45)}):Play()
    end)
    
    Btn.MouseEnter:Connect(function()
        Sounds.Hover:Play()
        TweenService:Create(Btn, TweenInfo.new(0.3), {BackgroundColor3 = Color3.fromRGB(0, 150, 255)}):Play()
    end)
    Btn.MouseLeave:Connect(function()
        TweenService:Create(Btn, TweenInfo.new(0.3), {BackgroundColor3 = Color3.fromRGB(0, 120, 220)}):Play()
    end)

    Btn.MouseButton1Click:Connect(function()
        local k = InputBox.Text
        if k == "" then return end
        
        Sounds.Click:Play()
        InputBox.TextEditable = false
        Btn.Active = false
        
        TweenService:Create(Btn, TweenInfo.new(0.2), {Size = UDim2.new(0.85, 0, 0, 40)}):Play()
        wait(0.1)
        TweenService:Create(Btn, TweenInfo.new(0.2), {Size = UDim2.new(0.9, 0, 0, 40)}):Play()
        
        BtnLabel.Text = "PROCESSING..."
        
        local success, err = pcall(function()
            local keyHash = Lib.sha256(k)
            local enc = Lib.b64_decode(ENCRYPTED_DATA)
            local iv = Lib.b64_decode(IV_DATA)
            
            task.spawn(function() ScrambleText(StatusTxt, "DECRYPTING PAYLOAD...", 2) end)
            
            local decrypted = Lib.Decrypt(enc, keyHash, iv, function(p)
                ProgressFill:TweenSize(UDim2.new(p, 0, 1, 0), "Out", "Quad", 0.1, true)
            end)
            
            ProgressFill.Size = UDim2.new(1,0,1,0)
            task.spawn(function() ScrambleText(StatusTxt, "VERIFYING SIGNATURE...", 0.5) end)
            task.wait(0.2)
            
            local clean = Lib.Unpad(decrypted)
            local func, syntaxErr = loadstring(clean)
            if not func then error("Invalid Key") end
            
            Sounds.Success:Play()
            StatusTxt.TextColor3 = Color3.fromRGB(0, 255, 150)
            ScrambleText(StatusTxt, "ACCESS GRANTED", 0.5)
            
            BtnLabel.Text = "SUCCESS"
            TweenService:Create(Btn, TweenInfo.new(0.5), {BackgroundColor3 = Color3.fromRGB(0, 200, 100)}):Play()
            
            task.wait(1)
            TweenService:Create(Main, TweenInfo.new(0.5, Enum.EasingStyle.Back, Enum.EasingDirection.In), {Size = UDim2.new(0,0,0,0), BackgroundTransparency = 1}):Play()
            wait(0.5)
            Screen:Destroy()
            task.spawn(func)
        end)
        
        if not success then
            Sounds.Fail:Play()
            StatusTxt.TextColor3 = Color3.fromRGB(255, 50, 50)
            ScrambleText(StatusTxt, "DECRYPTION FAILED", 0.5)
            
            warn(err)
            
            TweenService:Create(InputStroke, TweenInfo.new(0.1, Enum.EasingStyle.Sine, Enum.EasingDirection.InOut, 4, true), {Color = Color3.fromRGB(255, 0, 0)}):Play()
            BtnLabel.Text = "RETRY"
            
            wait(1.5)
            
            InputBox.TextEditable = true
            Btn.Active = true
            BtnLabel.Text = "INITIALIZE DECRYPTION"
            ProgressFill.Size = UDim2.new(0,0,1,0)
            StatusTxt.Text = "AWAITING INPUT"
            StatusTxt.TextColor3 = Color3.fromRGB(100, 100, 110)
            InputStroke.Color = Color3.fromRGB(40, 40, 45)
            TweenService:Create(Btn, TweenInfo.new(0.3), {BackgroundColor3 = Color3.fromRGB(0, 120, 220)}):Play()
        end
    end)

    local RunService = game:GetService("RunService")
    local Players = game:GetService("Players")
    local CoreGui = game:GetService("CoreGui")

    if RunService:IsStudio() then
       Screen.Parent = Players.LocalPlayer:WaitForChild("PlayerGui")
    else
    Screen.Parent = CoreGui
    end

    
    Intro()
    --#endregion
end

SecureRunner()
"""

def encrypt_logic(filepath, password):
    if not os.path.exists(filepath):
        print(f"Error: {filepath} not found.")
        return

    try:
        with open(filepath, 'rb') as f:
            raw_data = f.read()

        key = SHA256.new(password.encode('utf-8')).digest()
        iv = get_random_bytes(16)
        
        cipher = AES.new(key, AES.MODE_CBC, iv)
        ciphertext = cipher.encrypt(pad(raw_data, AES.block_size))
        
        b64_cipher = base64.b64encode(ciphertext).decode('utf-8')
        b64_iv = base64.b64encode(iv).decode('utf-8')

        final_lua = LUA_TEMPLATE.replace("{ENCRYPTED_PAYLOAD}", b64_cipher)
        final_lua = final_lua.replace("{IV_PAYLOAD}", b64_iv)

        with open("obfuscated.lua", "w", encoding='utf-8') as f:
            f.write(final_lua)
            
        print("\n[SUCCESS] Script Encrypted.")
        print(f"Key: {password}")

    except Exception as e:
        print(f"Error: {e}")

if __name__ == "__main__":
    print("--- WELCOME TO NEKO'S LUA AES-256 SECURE LOADER CREATION TOOL ---")
    target_file = ""
    if len(sys.argv) > 1:
        target_file = sys.argv[1]
    else:
        target_file = input("Drag Lua file here: ").strip().replace('"', '')

    if not target_file: sys.exit()
    
    pwd = input("Enter Password: ")
    if not pwd: sys.exit()

    encrypt_logic(target_file, pwd)