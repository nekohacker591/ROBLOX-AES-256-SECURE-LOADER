import sys
import base64
import os
import random
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad
from Crypto.Random import get_random_bytes

# =============================================================================
# THE LUA AES ENGINE (The core decryption logic)
# =============================================================================
LUA_AES_ENGINE = r"""
local bit = bit32
local bxor, band, rshift, lshift = bit.bxor, bit.band, bit.rshift, bit.lshift
local char, byte, sub, concat = string.char, string.byte, string.sub, table.concat
local b64chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'
local b64map = {}
for i = 1, 64 do b64map[sub(b64chars, i, i)] = i - 1 end

local function DecB64(d)
    d = string.gsub(d, '[^' .. b64chars .. '=]', '')
    local t = {}
    for i = 1, #d, 4 do
        local a, b, c, d_b = byte(d, i, i + 3)
        local v = lshift(b64map[char(a)], 18) + lshift(b64map[char(b)], 12) + lshift(b64map[char(c) or "A"] or 0, 6) + (b64map[char(d_b) or "A"] or 0)
        table.insert(t, char(band(rshift(v, 16), 0xFF)))
        if c ~= 61 then table.insert(t, char(band(rshift(v, 8), 0xFF))) end
        if d_b ~= 61 then table.insert(t, char(band(v, 0xFF))) end
    end
    return concat(t)
end

local SBox = {0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16}
local InvSBox = {}
for i = 1, 256 do InvSBox[SBox[i] + 1] = i - 1 end
local Rcon = {0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36}

local function GMul(a, b)
    local p = 0
    for i = 1, 8 do
        if band(b, 1) == 1 then p = bxor(p, a) end
        local hi = band(a, 0x80)
        a = band(lshift(a, 1), 0xFF)
        if hi == 0x80 then a = bxor(a, 0x1b) end
        b = rshift(b, 1)
    end
    return p
end

local function ExKey(keyBytes)
    local w = {}
    for i = 1, 32 do w[i] = keyBytes[i] end
    local i, wm = 33, 8
    while wm < 60 do
        local t = {w[i - 4], w[i - 3], w[i - 2], w[i - 1]}
        if wm % 8 == 0 then
            local x = t[1]; t[1], t[2], t[3], t[4] = t[2], t[3], t[4], x
            for j = 1, 4 do t[j] = SBox[t[j] + 1] end
            t[1] = bxor(t[1], Rcon[math.floor(wm / 8)])
        elseif wm % 8 == 4 then
            for j = 1, 4 do t[j] = SBox[t[j] + 1] end
        end
        for j = 1, 4 do w[i] = bxor(w[i - 32], t[j]); i = i + 1 end
        wm = wm + 1
    end
    return w
end

function RunDecrypt(enc, keyStr, ivStr)
    local k = {}
    while #k < 32 do
        for i = 1, #keyStr do table.insert(k, byte(keyStr, i)) end
    end
    while #k > 32 do table.remove(k) end
    local iv = {}
    local div = DecB64(ivStr)
    for i = 1, 16 do table.insert(iv, byte(div, i) or 0) end
    local ek = ExKey(k)
    local raw = DecB64(enc)
    local out = {}
    local pb = iv
    for i = 1, #raw, 16 do
        local blk = {byte(raw, i, i + 15)}
        if #blk < 16 then break end
        local st = {table.unpack(blk)}
        local function AddRoundKey(s, r)
            local o = r * 16
            for j = 1, 16 do s[j] = bxor(s[j], ek[o + j]) end
        end
        AddRoundKey(st, 14)
        for r = 13, 1, -1 do
            local t = {st[1],st[14],st[11],st[8],st[5],st[2],st[15],st[12],st[9],st[6],st[3],st[16],st[13],st[10],st[7],st[4]}
            for j = 1, 16 do st[j] = InvSBox[t[j] + 1] end
            AddRoundKey(st, r)
            local u = {table.unpack(st)}
            for c = 0, 3 do
                local x = c * 4
                st[x + 1] = bxor(GMul(0x0e, u[x + 1]), GMul(0x0b, u[x + 2]), GMul(0x0d, u[x + 3]), GMul(0x09, u[x + 4]))
                st[x + 2] = bxor(GMul(0x09, u[x + 1]), GMul(0x0e, u[x + 2]), GMul(0x0b, u[x + 3]), GMul(0x0d, u[x + 4]))
                st[x + 3] = bxor(GMul(0x0d, u[x + 1]), GMul(0x09, u[x + 2]), GMul(0x0e, u[x + 3]), GMul(0x0b, u[x + 4]))
                st[x + 4] = bxor(GMul(0x0b, u[x + 1]), GMul(0x0d, u[x + 2]), GMul(0x09, u[x + 3]), GMul(0x0e, u[x + 4]))
            end
        end
        local t = {st[1],st[14],st[11],st[8],st[5],st[2],st[15],st[12],st[9],st[6],st[3],st[16],st[13],st[10],st[7],st[4]}
        for j = 1, 16 do st[j] = InvSBox[t[j] + 1] end
        AddRoundKey(st, 0)
        for j = 1, 16 do table.insert(out, char(bxor(st[j], pb[j]))) end
        pb = blk
    end
    local p = byte(out[#out])
    if p and p > 0 and p <= 16 then
        for _ = 1, p do table.remove(out) end
    end
    return concat(out)
end
"""

# =============================================================================
# THE SECURE GATEWAY UI (Original Slick Version)
# =============================================================================
CLIENT_UI_LUA = r"""
local REMOTE_NAME = "{REMOTE_NAME}"
local P = game:GetService("Players").LocalPlayer
local Screen = Instance.new("ScreenGui", P:WaitForChild("PlayerGui"))
Screen.Name = "SecureLoader"; Screen.ResetOnSpawn = false; Screen.IgnoreGuiInset = true
local Sounds = { Spawn = Instance.new("Sound", Screen), Click = Instance.new("Sound", Screen), Hover = Instance.new("Sound", Screen), Success = Instance.new("Sound", Screen), Fail = Instance.new("Sound", Screen) }
Sounds.Spawn.SoundId="rbxassetid://3320590485"; Sounds.Click.SoundId="rbxassetid://6042053626"; Sounds.Hover.SoundId="rbxassetid://6895079853"; Sounds.Success.SoundId="rbxassetid://101176804827210"; Sounds.Fail.SoundId="rbxassetid://87519554692663"
local Main = Instance.new("Frame", Screen)
Main.Size = UDim2.new(0, 360, 0, 200); Main.Position = UDim2.new(0.5, -180, 0.5, -80); Main.BackgroundColor3 = Color3.fromRGB(15, 15, 17); Main.BackgroundTransparency = 1; Main.Active = true; Main.Draggable = true
Instance.new("UICorner", Main).CornerRadius = UDim.new(0, 12); local Stroke = Instance.new("UIStroke", Main); Stroke.Color = Color3.fromRGB(60, 60, 70); Stroke.Thickness = 1; Stroke.Transparency = 0.6
local Header = Instance.new("TextLabel", Main); Header.Text = "SECURE GATEWAY"; Header.Size = UDim2.new(1, -40, 0, 50); Header.Position = UDim2.new(0, 20, 0, 0); Header.BackgroundTransparency = 1; Header.TextColor3 = Color3.fromRGB(240, 240, 240); Header.Font = Enum.Font.GothamBold; Header.TextSize = 14; Header.TextXAlignment = Enum.TextXAlignment.Left
local InputFrame = Instance.new("Frame", Main); InputFrame.Size = UDim2.new(0.9, 0, 0, 45); InputFrame.Position = UDim2.new(0.05, 0, 0, 60); InputFrame.BackgroundColor3 = Color3.fromRGB(10, 10, 12); Instance.new("UICorner", InputFrame).CornerRadius = UDim.new(0, 8); local InputStroke = Instance.new("UIStroke", InputFrame); InputStroke.Color = Color3.fromRGB(40, 40, 45); InputStroke.Thickness = 1
local InputBox = Instance.new("TextBox", InputFrame); InputBox.Size = UDim2.new(1, -20, 1, 0); InputBox.Position = UDim2.new(0, 10, 0, 0); InputBox.BackgroundTransparency = 1; InputBox.TextColor3 = Color3.fromRGB(255, 255, 255); InputBox.PlaceholderColor3 = Color3.fromRGB(100, 100, 110); InputBox.PlaceholderText = "Enter Decryption Key"; InputBox.Text = ""; InputBox.Font = Enum.Font.GothamMedium; InputBox.TextSize = 14; InputBox.TextXAlignment = Enum.TextXAlignment.Left
local Btn = Instance.new("TextButton", Main); Btn.Size = UDim2.new(0.9, 0, 0, 40); Btn.Position = UDim2.new(0.05, 0, 1, -50); Btn.BackgroundColor3 = Color3.fromRGB(0, 120, 220); Btn.Text = "INITIALIZE"; Btn.Font = Enum.Font.GothamBold; Btn.TextColor3 = Color3.fromRGB(255, 255, 255); Btn.TextSize = 12; Instance.new("UICorner", Btn).CornerRadius = UDim.new(0, 8)
Sounds.Spawn:Play(); game:GetService("TweenService"):Create(Main, TweenInfo.new(0.6, Enum.EasingStyle.Quart, Enum.EasingDirection.Out), {Position = UDim2.new(0.5, -180, 0.5, -100), BackgroundTransparency = 0}):Play()
local Rem = game:GetService("ReplicatedStorage"):WaitForChild(REMOTE_NAME, 15)
Btn.MouseButton1Click:Connect(function() if Rem then Sounds.Click:Play(); Rem:FireServer(InputBox.Text); Btn.Text = "DECRYPTING..." end end)
if Rem then Rem.OnClientEvent:Connect(function(m) if m == "SUCCESS" then Sounds.Success:Play(); Btn.Text = "ACCESS GRANTED"; wait(1); Screen:Destroy() else Sounds.Fail:Play(); Btn.Text = "AUTH FAILED"; wait(1); Btn.Text = "INITIALIZE" end end) end
"""

# =============================================================================
# MAIN CLONING LOGIC
# =============================================================================
MAIN_LOGIC = r"""
local plr_name, module_ref = ...
local plr = game:GetService("Players"):FindFirstChild(plr_name)
local folder = module_ref:FindFirstChild("Main")
if plr and folder then
    local s = folder:FindFirstChild("ServerHandler")
    local l = folder:FindFirstChild("ClientUI")
    if s then local c = s:Clone(); c.Disabled = false; c.Parent = game:GetService("ServerScriptService") end
    if l then local c = l:Clone(); c.Disabled = false; c.Parent = plr:WaitForChild("PlayerGui") end
end
"""

def encrypt_aes(data, key_str):
    k = key_str
    while len(k) < 32: k += key_str
    k_bytes = k[:32].encode('utf-8')
    iv = get_random_bytes(16)
    cipher = AES.new(k_bytes, AES.MODE_CBC, iv)
    ct = cipher.encrypt(pad(data.encode('utf-8'), AES.block_size))
    return base64.b64encode(ct).decode(), base64.b64encode(iv).decode()

def main():
    if len(sys.argv) < 4:
        print("Usage: python main.py <lua_file> <username> <password>")
        sys.exit(1)

    target_file = sys.argv[1].replace('"', '')
    username = sys.argv[2]
    password = sys.argv[3]

    if not os.path.exists(target_file):
        print(f"Error: {target_file} not found.")
        sys.exit(1)

    with open(target_file, 'r', encoding='utf-8') as f: target_code = f.read()

    # 1. Payload & Remote Prep
    server_enc, server_iv = encrypt_aes(target_code, password)
    remote_name = "Auth_" + base64.b64encode(os.urandom(4)).decode().replace("=","")
    
    server_src = f'local REMOTE_NAME = "{remote_name}"\nlocal ENC_PAYLOAD = "{server_enc}"\nlocal ENC_IV = "{server_iv}"\nlocal VM_ID = 13767327314\nlocal RS = game:GetService("ReplicatedStorage")\nlocal Rem = RS:FindFirstChild(REMOTE_NAME) or Instance.new("RemoteEvent")\nRem.Name = REMOTE_NAME; Rem.Parent = RS\n\n{LUA_AES_ENGINE}\n\nRem.OnServerEvent:Connect(function(p, key)\n    local s, code = pcall(function() return RunDecrypt(ENC_PAYLOAD, key, ENC_IV) end)\n    if s and #code > 10 then\n        local vm = require(VM_ID); local exe = vm(code)\n        if exe then Rem:FireClient(p, "SUCCESS"); task.spawn(exe) else Rem:FireClient(p, "FAIL") end\n    else Rem:FireClient(p, "FAIL") end\nend)'
    client_src = CLIENT_UI_LUA.replace("{REMOTE_NAME}", remote_name)

    # 2. Main Module Logic Encryption (Key = Username)
    logic_enc, logic_iv = encrypt_aes(MAIN_LOGIC, username)
    module_src = f'local VM_ID = 13767327314\nlocal ENC_DATA = "{logic_enc}"\n{LUA_AES_ENGINE}\n\nreturn function(u, i)\n    if u ~= "{username}" then warn("Auth Fail") return end\n    local s, plain = pcall(function() return RunDecrypt(ENC_DATA, u, i) end)\n    if s and #plain > 5 then\n        local vm = require(VM_ID); local f = vm(plain)\n        if f then task.spawn(f, u, script) end\n    else warn("Decryption Failure") end\nend'

    # 3. XML Construction (Clean logic, no bloat)
    xml = f"""<roblox xmlns:xmime="http://www.w3.org/2005/05/xmlmime" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xsi:noNamespaceSchemaLocation="http://www.roblox.com/roblox.xsd" version="4">
	<Item class="ModuleScript" referent="RBX_MODULE">
		<Properties>
			<ProtectedString name="Source"><![CDATA[{module_src}]]></ProtectedString>
			<string name="Name">MainModule</string>
		</Properties>
		<Item class="Folder" referent="RBX_FOLDER">
			<Properties><string name="Name">Main</string></Properties>
			<Item class="Script" referent="RBX_SERVER">
				<Properties><bool name="Disabled">true</bool><ProtectedString name="Source"><![CDATA[{server_src}]]></ProtectedString><string name="Name">ServerHandler</string></Properties>
			</Item>
			<Item class="LocalScript" referent="RBX_CLIENT">
				<Properties><bool name="Disabled">true</bool><ProtectedString name="Source"><![CDATA[{client_src}]]></ProtectedString><string name="Name">ClientUI</string></Properties>
			</Item>
		</Item>
	</Item>
</roblox>"""

    out_file = f"TEST_CLEAN_{username}.rbxmx"
    with open(out_file, "w", encoding="utf-8") as f: f.write(xml)

    # 4. Loader Generation
    req_ascii = "".join([f"\\{ord(c)}" for c in "require"])
    loader = f'getfenv()["{req_ascii}"](ASSET_ID)("{username}", "{logic_iv}")'
    with open("loader.txt", "w", encoding="utf-8") as f: f.write(loader)

    print(f"\n[SUCCESS] Generated: {out_file}")
    print(f"MainModule Key: {username}")
    print(f"IV: {logic_iv}")
    print(f"One-liner: {loader}")

if __name__ == "__main__":
    main()
