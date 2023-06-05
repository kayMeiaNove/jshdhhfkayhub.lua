_G.mudar_avatar = false
while (true) do
	wait(_G.delayskin)
    if (_G.mudar_avatar == true) then
        local args = {
            [1] = "LoadAvatar",
            [2] = {
                ["Waist"] = 0,
                ["Mask"] = math.random(1, 20),
                ["Glasses"] = math.random(1, 20),
                ["Tone"] = math.random(1, 2),
                ["LastName"] = "kay",
                ["HeadPhones"] = 4,
                ["Backpack"] = math.random(1, 20),
                ["Genre"] = "Male",
                ["Name"] = "k",
                ["Hats"] = math.random(1, 20),
                ["Pants"] = math.random(1, 30),
                ["Face"] = math.random(1, 20),
                ["Shirt"] = math.random(1, 20),
                ["Hair"] = math.random(1, 20)
                }
            }
            game:GetService("ReplicatedStorage").Remotes.Handler:FireServer(unpack(args))
        else

        end
end
