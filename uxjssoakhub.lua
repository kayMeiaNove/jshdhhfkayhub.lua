local id_jogo_jogador = game.PlaceId
local scripts_hub = "https://raw.githubusercontent.com/tvgueimer84/jshdhhfkayhub/main/"
local jogos = {'8007761278', '9103898828'}

for i, id in ipairs(jogos) do	
    if id == tostring(id_jogo_jogador) then
        loadstring(game:HttpGet(scripts_hub..id_jogo_jogador..".lua"))()
        jogo_suportado = true
        break
    end
end
if not jogo_suportado then
    game.Players.LocalPlayer:Kick("kayhub is not supported on this game!")
end
