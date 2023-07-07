local id_jogo_jogador = game.PlaceId
local tabela = {'8007761278', '9103898828'}
local scripts_hub = "https://raw.githubusercontent.com/tvgueimer84/jshdhhfkayhub/main/"
local jogo_suportado 
for i, id in ipairs(tabela) do
  if id == tostring(id_jogo_jogador) then
    jogo_suportado = true
    loadstring(game:HttpGet(scripts_hub..id_jogo_jogador..".lua"))()
  end
end
if not jogo_suportado then
				game.Players.LocalPlayer:Kick("kayhub is not supported on this game!")
end
