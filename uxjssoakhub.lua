

local h = "unpack";
local s = "ldexp";
local n = "insert";
local i = "rep";
local o = "gsub";
local a = "sub";
local t = "char";
local e = "byte";
local StrToNumber = tonumber;
local Byte = string[e];
local Char = string[t];
local Sub = string[a];
local Subg = string[o];
local Rep = string[i];
local Concat = table.concat;
local Insert = table[n];
local LDExp = math[s];
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table[h];
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local r = 1;
	local DIP = r;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		local d = 2;
		if (Byte(byte, d) == 79) then
			local c = 1;
			local l = 1;
			repeatNext = StrToNumber(Sub(byte, l, c));
			return "";
		else
			local u = 16;
			local a = Char(StrToNumber(byte, u));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local g = 1;
			local f = 1;
			local w = 1;
			local m = 2;
			local Res = (Bit / (2 ^ (Start - 1))) % (m ^ (((End - w) - (Start - 1)) + f));
			return Res - (Res % g);
		else
			local y = 1;
			local Plc = 2 ^ (Start - y);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local p = 1;
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + p;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local k = 16777216;
		local v = 4;
		local b = 3;
		local a, b, c, d = Byte(ByteString, DIP, DIP + b);
		DIP = DIP + v;
		return (d * k) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local R = 52;
		local H = 2;
		local O = 0;
		local A = 1;
		local T = 1;
		local E = 32;
		local z = 21;
		local q = 2;
		local j = 20;
		local x = 1;
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = x;
		local Mantissa = (gBit(Right, 1, j) * (q ^ 32)) + Left;
		local Exponent = gBit(Right, z, 31);
		local Sign = ((gBit(Right, E) == T) and -A) or 1;
		if (Exponent == O) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				local I = 0;
				Exponent = 1;
				IsNormal = I;
			end
		else
			local N = 2047;
			if (Exponent == N) then
				local S = 1;
				return ((Mantissa == 0) and (Sign * (S / 0))) or (Sign * NaN);
			end
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (H ^ R)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		local L = "#";
		local D = 1;
		return {...}, Select(L, ...);
	end
	local function Deserialize()
		local B = 1;
		local P = 3;
		local F = 1;
		local W = nil;
		local M = 3;
		local U = 2;
		local C = 1;
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,W,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = F, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				local G = 0;
				Cons = gBits8() ~= G;
			elseif (Type == 2) then
				Cons = gFloat();
			else
				local Y = 3;
				if (Type == Y) then
					Cons = gString();
				end
			end
			Consts[Idx] = Cons;
		end
		Chunk[P] = gBits8();
		for Idx = B, gBits32() do
			local V = 0;
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == V) then
				local Zl = 1;
				local Zd = 1;
				local Ze = 4;
				local Z = nil;
				local Q = 3;
				local J = 2;
				local X = 4;
				local K = 3;
				local Type = gBit(Descriptor, 2, K);
				local Mask = gBit(Descriptor, X, 6);
				local Inst = {gBits16(),gBits16(),Z,nil};
				if (Type == 0) then
					local Za = 4;
					local Zt = 3;
					Inst[Zt] = gBits16();
					Inst[Za] = gBits16();
				else
					local Zo = 1;
					if (Type == Zo) then
						local Zi = 3;
						Inst[Zi] = gBits32();
					elseif (Type == 2) then
						local Zs = 2;
						local Zn = 3;
						Inst[Zn] = gBits32() - (Zs ^ 16);
					elseif (Type == 3) then
						local Zr = 4;
						local Zh = 16;
						Inst[3] = gBits32() - (2 ^ Zh);
						Inst[Zr] = gBits16();
					end
				end
				if (gBit(Mask, 1, Zd) == Zl) then
					local Zu = 2;
					local Zc = 2;
					Inst[Zc] = Consts[Inst[Zu]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Zw = 3;
		local Zm = 2;
		local Instr = Chunk[1];
		local Proto = Chunk[Zm];
		local Params = Chunk[Zw];
		return function(...)
			local Zg = 0;
			local Zf = "#";
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select(Zf, ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = Zg, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					local Zy = 1;
					Stk[Idx] = Args[Idx + Zy];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 42) then
					if (Enum <= 20) then
						if (Enum <= 9) then
							local Zp = 4;
							if (Enum <= Zp) then
								if (Enum <= 1) then
									local Zb = 0;
									if (Enum == Zb) then
										local Zk = 4;
										local Zv = 2;
										if (Stk[Inst[Zv]] == Stk[Inst[Zk]]) then
											local Zx = 1;
											VIP = VIP + Zx;
										else
											VIP = Inst[3];
										end
									else
										local Zq = 4;
										local Zj = 2;
										Stk[Inst[Zj]] = Stk[Inst[3]][Inst[Zq]];
									end
								else
									local Zz = 2;
									if (Enum <= Zz) then
										local ZT = 3;
										local ZE = 1;
										local A = Inst[2];
										local Results, Limit = _R(Stk[A](Unpack(Stk, A + ZE, Inst[ZT])));
										Top = (Limit + A) - 1;
										local Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									elseif (Enum > 3) then
										local ZA = 2;
										Stk[Inst[ZA]]();
									else
										local ZI = 3;
										local ZO = 2;
										Stk[Inst[ZO]] = Inst[ZI] ~= 0;
									end
								end
							else
								local ZN = 6;
								if (Enum <= ZN) then
									local ZS = 5;
									if (Enum == ZS) then
										Stk[Inst[2]]();
									else
										local ZH = 1;
										local A = Inst[2];
										Stk[A] = Stk[A](Stk[A + ZH]);
									end
								elseif (Enum <= 7) then
									local ZR = 2;
									Stk[Inst[ZR]] = Stk[Inst[3]][Inst[4]];
								elseif (Enum > 8) then
									local ZC = 4;
									local ZL = 1;
									local ZD = 2;
									local A = Inst[ZD];
									local B = Stk[Inst[3]];
									Stk[A + ZL] = B;
									Stk[A] = B[Inst[ZC]];
								else
									local ZU = 3;
									VIP = Inst[ZU];
								end
							end
						else
							local ZM = 14;
							if (Enum <= ZM) then
								if (Enum <= 11) then
									if (Enum > 10) then
										local A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									else
										local ZW = 3;
										local A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[ZW]));
									end
								elseif (Enum <= 12) then
									local ZF = 3;
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[ZF]));
								elseif (Enum == 13) then
									local ZG = 2;
									Stk[Inst[ZG]][Inst[3]] = Stk[Inst[4]];
								else
									local ZY = 3;
									Stk[Inst[2]] = Upvalues[Inst[ZY]];
								end
							else
								local ZP = 17;
								if (Enum <= ZP) then
									local ZB = 15;
									if (Enum <= ZB) then
										local ZK = 4;
										local ZV = 2;
										if (Stk[Inst[ZV]] == Inst[ZK]) then
											VIP = VIP + 1;
										else
											local ZX = 3;
											VIP = Inst[ZX];
										end
									else
										local ZJ = 16;
										if (Enum == ZJ) then
											local ZZ = 1;
											local ZQ = 2;
											local A = Inst[ZQ];
											Stk[A] = Stk[A](Unpack(Stk, A + ZZ, Top));
										else
											local ZZt = 3;
											local ZZe = 2;
											Stk[Inst[ZZe]] = Stk[Inst[ZZt]] + Inst[4];
										end
									end
								elseif (Enum <= 18) then
									local ZZi = 1;
									local ZZo = 2;
									local ZZa = 4;
									local A = Inst[2];
									local C = Inst[ZZa];
									local CB = A + ZZo;
									local Result = {Stk[A](Stk[A + 1], Stk[CB])};
									for Idx = 1, C do
										Stk[CB + Idx] = Result[Idx];
									end
									local R = Result[ZZi];
									if R then
										local ZZn = 3;
										Stk[CB] = R;
										VIP = Inst[ZZn];
									else
										local ZZs = 1;
										VIP = VIP + ZZs;
									end
								elseif (Enum > 19) then
									local ZZh = 2;
									if Stk[Inst[ZZh]] then
										VIP = VIP + 1;
									else
										local ZZr = 3;
										VIP = Inst[ZZr];
									end
								else
									local ZZd = 3;
									local A = Inst[2];
									local B = Stk[Inst[ZZd]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							end
						end
					else
						local ZZl = 31;
						if (Enum <= ZZl) then
							if (Enum <= 25) then
								local ZZc = 22;
								if (Enum <= ZZc) then
									if (Enum == 21) then
										local ZZm = 4;
										local ZZu = 3;
										Stk[Inst[2]] = Stk[Inst[ZZu]] % Inst[ZZm];
									else
										local ZZy = 0;
										local ZZg = 1;
										local ZZf = 1;
										local ZZw = 2;
										local A = Inst[ZZw];
										local Results, Limit = _R(Stk[A](Unpack(Stk, A + ZZf, Top)));
										Top = (Limit + A) - ZZg;
										local Edx = ZZy;
										for Idx = A, Top do
											local ZZp = 1;
											Edx = Edx + ZZp;
											Stk[Idx] = Results[Edx];
										end
									end
								elseif (Enum <= 23) then
									local ZZb = 4;
									if (Stk[Inst[2]] < Inst[ZZb]) then
										VIP = VIP + 1;
									else
										local ZZv = 3;
										VIP = Inst[ZZv];
									end
								else
									local ZZk = 24;
									if (Enum == ZZk) then
										local ZZx = 1;
										local A = Inst[2];
										local T = Stk[A];
										for Idx = A + ZZx, Top do
											Insert(T, Stk[Idx]);
										end
									else
										local ZZz = 3;
										local ZZq = 1;
										local ZZj = 2;
										local A = Inst[ZZj];
										Stk[A] = Stk[A](Unpack(Stk, A + ZZq, Inst[ZZz]));
									end
								end
							else
								local ZZE = 28;
								if (Enum <= ZZE) then
									local ZZT = 26;
									if (Enum <= ZZT) then
										local ZZA = 2;
										Stk[Inst[ZZA]] = Upvalues[Inst[3]];
									elseif (Enum == 27) then
										local ZZI = 4;
										local ZZO = 3;
										Stk[Inst[2]] = Stk[Inst[ZZO]] + Stk[Inst[ZZI]];
									else
										local ZZS = 4;
										local ZZN = 3;
										Stk[Inst[2]] = Stk[Inst[ZZN]] - Inst[ZZS];
									end
								else
									local ZZH = 29;
									if (Enum <= ZZH) then
										local ZZD = 3;
										local ZZR = 2;
										local A = Inst[ZZR];
										local T = Stk[A];
										local B = Inst[ZZD];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									elseif (Enum > 30) then
										local ZZZ = 2;
										local ZZY = 4;
										local ZZG = 1;
										local ZZW = "__newindex";
										local ZZC = "__index";
										local ZZL = 3;
										local NewProto = Proto[Inst[ZZL]];
										local NewUvals;
										local Indexes = {};
										NewUvals = Setmetatable({}, {[ZZC]=function(_, Key)
											local ZZM = 2;
											local ZZU = 1;
											local Val = Indexes[Key];
											return Val[ZZU][Val[ZZM]];
										end,[ZZW]=function(_, Key, Value)
											local ZZF = 2;
											local Val = Indexes[Key];
											Val[1][Val[ZZF]] = Value;
										end});
										for Idx = ZZG, Inst[ZZY] do
											local ZZQ = 1;
											local ZZB = 52;
											local ZZP = 1;
											VIP = VIP + ZZP;
											local Mvm = Instr[VIP];
											if (Mvm[1] == ZZB) then
												local ZZK = 2;
												local ZZV = 1;
												Indexes[Idx - ZZV] = {Stk,Mvm[3]};
											else
												local ZZJ = 2;
												local ZZX = 1;
												Indexes[Idx - 1] = {Upvalues,Mvm[3]};
											end
											Lupvals[#Lupvals + ZZQ] = Indexes;
										end
										Stk[Inst[ZZZ]] = Wrap(NewProto, NewUvals, Env);
									else
										local ZZZe = 4;
										if (Stk[Inst[2]] == Inst[ZZZe]) then
											VIP = VIP + 1;
										else
											local ZZZt = 3;
											VIP = Inst[ZZZt];
										end
									end
								end
							end
						elseif (Enum <= 36) then
							if (Enum <= 33) then
								local ZZZa = 32;
								if (Enum > ZZZa) then
									if not Stk[Inst[2]] then
										local ZZZo = 1;
										VIP = VIP + ZZZo;
									else
										local ZZZi = 3;
										VIP = Inst[ZZZi];
									end
								else
									Stk[Inst[2]] = {};
								end
							elseif (Enum <= 34) then
								local ZZZs = 4;
								local ZZZn = 2;
								if (Stk[Inst[ZZZn]] ~= Stk[Inst[ZZZs]]) then
									local ZZZh = 1;
									VIP = VIP + ZZZh;
								else
									local ZZZr = 3;
									VIP = Inst[ZZZr];
								end
							elseif (Enum == 35) then
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									local ZZZd = 1;
									Edx = Edx + ZZZd;
									Stk[Idx] = Results[Edx];
								end
							else
								local ZZZc = 4;
								local ZZZl = 2;
								Stk[Inst[ZZZl]] = Stk[Inst[3]] - Stk[Inst[ZZZc]];
							end
						else
							local ZZZu = 39;
							if (Enum <= ZZZu) then
								if (Enum <= 37) then
									local ZZZm = 2;
									for Idx = Inst[ZZZm], Inst[3] do
										Stk[Idx] = nil;
									end
								else
									local ZZZw = 38;
									if (Enum > ZZZw) then
										local ZZZp = 1;
										local ZZZy = 1;
										local ZZZg = 2;
										local ZZZf = 2;
										local A = Inst[ZZZf];
										local C = Inst[4];
										local CB = A + ZZZg;
										local Result = {Stk[A](Stk[A + 1], Stk[CB])};
										for Idx = 1, C do
											Stk[CB + Idx] = Result[Idx];
										end
										local R = Result[ZZZp];
										if R then
											local ZZZb = 3;
											Stk[CB] = R;
											VIP = Inst[ZZZb];
										else
											VIP = VIP + 1;
										end
									else
										local ZZZx = 0;
										local ZZZk = 1;
										local ZZZv = 2;
										local A = Inst[ZZZv];
										local Results = {Stk[A](Stk[A + 1])};
										local Edx = ZZZx;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									end
								end
							elseif (Enum <= 40) then
								local ZZZT = 4;
								local ZZZE = 1;
								local ZZZz = "__newindex";
								local ZZZq = "__index";
								local ZZZj = 3;
								local NewProto = Proto[Inst[ZZZj]];
								local NewUvals;
								local Indexes = {};
								NewUvals = Setmetatable({}, {[ZZZq]=function(_, Key)
									local Val = Indexes[Key];
									return Val[1][Val[2]];
								end,[ZZZz]=function(_, Key, Value)
									local Val = Indexes[Key];
									Val[1][Val[2]] = Value;
								end});
								for Idx = ZZZE, Inst[ZZZT] do
									local ZZZD = 1;
									local ZZZO = 1;
									local ZZZA = 1;
									VIP = VIP + ZZZA;
									local Mvm = Instr[VIP];
									if (Mvm[ZZZO] == 52) then
										local ZZZN = 2;
										local ZZZI = 1;
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										local ZZZR = 2;
										local ZZZH = 1;
										local ZZZS = 1;
										Indexes[Idx - ZZZS] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + ZZZD] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							elseif (Enum == 41) then
								if Stk[Inst[2]] then
									local ZZZL = 1;
									VIP = VIP + ZZZL;
								else
									VIP = Inst[3];
								end
							else
								local ZZZC = 2;
								Stk[Inst[ZZZC]] = Stk[Inst[3]] + Inst[4];
							end
						end
					end
				else
					local ZZZU = 64;
					if (Enum <= ZZZU) then
						if (Enum <= 53) then
							local ZZZM = 47;
							if (Enum <= ZZZM) then
								local ZZZW = 44;
								if (Enum <= ZZZW) then
									if (Enum == 43) then
										for Idx = Inst[2], Inst[3] do
											Stk[Idx] = nil;
										end
									else
										local ZZZF = 1;
										local A = Inst[2];
										local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
										Top = (Limit + A) - ZZZF;
										local Edx = 0;
										for Idx = A, Top do
											local ZZZG = 1;
											Edx = Edx + ZZZG;
											Stk[Idx] = Results[Edx];
										end
									end
								else
									local ZZZY = 45;
									if (Enum <= ZZZY) then
										local ZZZP = 3;
										Upvalues[Inst[ZZZP]] = Stk[Inst[2]];
									elseif (Enum == 46) then
										Stk[Inst[2]] = Env[Inst[3]];
									else
										local ZZZB = 3;
										Stk[Inst[2]] = #Stk[Inst[ZZZB]];
									end
								end
							else
								local ZZZV = 50;
								if (Enum <= ZZZV) then
									if (Enum <= 48) then
										Stk[Inst[2]] = Inst[3] ~= 0;
									elseif (Enum > 49) then
										local ZZZK = 2;
										local A = Inst[ZZZK];
										Stk[A] = Stk[A]();
									else
										local ZZZJ = 3;
										local ZZZX = 2;
										Stk[Inst[ZZZX]] = Env[Inst[ZZZJ]];
									end
								else
									local ZZZQ = 51;
									if (Enum <= ZZZQ) then
										local ZZZZe = 3;
										local ZZZZ = 2;
										local A = Inst[ZZZZ];
										local T = Stk[A];
										local B = Inst[ZZZZe];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									else
										local ZZZZt = 52;
										if (Enum == ZZZZt) then
											local ZZZZa = 2;
											Stk[Inst[ZZZZa]] = Stk[Inst[3]];
										else
											local ZZZZi = 0;
											local ZZZZo = 2;
											local A = Inst[ZZZZo];
											local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
											Top = (Limit + A) - 1;
											local Edx = ZZZZi;
											for Idx = A, Top do
												Edx = Edx + 1;
												Stk[Idx] = Results[Edx];
											end
										end
									end
								end
							end
						elseif (Enum <= 58) then
							local ZZZZn = 55;
							if (Enum <= ZZZZn) then
								if (Enum > 54) then
									local ZZZZh = 4;
									local ZZZZs = 2;
									Stk[Inst[ZZZZs]][Inst[3]] = Stk[Inst[ZZZZh]];
								else
									local ZZZZd = 4;
									local ZZZZr = 2;
									if (Stk[Inst[ZZZZr]] ~= Stk[Inst[ZZZZd]]) then
										local ZZZZl = 1;
										VIP = VIP + ZZZZl;
									else
										local ZZZZc = 3;
										VIP = Inst[ZZZZc];
									end
								end
							else
								local ZZZZu = 56;
								if (Enum <= ZZZZu) then
									local ZZZZw = 3;
									local ZZZZm = 2;
									Stk[Inst[ZZZZm]] = Inst[ZZZZw];
								elseif (Enum > 57) then
									do
										return;
									end
								else
									local ZZZZg = 0;
									local ZZZZf = 2;
									local A = Inst[ZZZZf];
									local Step = Stk[A + 2];
									local Index = Stk[A] + Step;
									Stk[A] = Index;
									if (Step > ZZZZg) then
										if (Index <= Stk[A + 1]) then
											VIP = Inst[3];
											Stk[A + 3] = Index;
										end
									elseif (Index >= Stk[A + 1]) then
										local ZZZZy = 3;
										VIP = Inst[ZZZZy];
										Stk[A + 3] = Index;
									end
								end
							end
						else
							local ZZZZp = 61;
							if (Enum <= ZZZZp) then
								if (Enum <= 59) then
									local ZZZZv = 2;
									local ZZZZb = 1;
									local B = Inst[3];
									local K = Stk[B];
									for Idx = B + ZZZZb, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[ZZZZv]] = K;
								else
									local ZZZZk = 60;
									if (Enum > ZZZZk) then
										local ZZZZj = 1;
										local ZZZZx = 2;
										local A = Inst[ZZZZx];
										local T = Stk[A];
										for Idx = A + ZZZZj, Top do
											Insert(T, Stk[Idx]);
										end
									else
										local ZZZZz = 2;
										local ZZZZq = 2;
										local A = Inst[ZZZZq];
										local Step = Stk[A + ZZZZz];
										local Index = Stk[A] + Step;
										Stk[A] = Index;
										if (Step > 0) then
											local ZZZZE = 1;
											if (Index <= Stk[A + ZZZZE]) then
												local ZZZZT = 3;
												VIP = Inst[3];
												Stk[A + ZZZZT] = Index;
											end
										elseif (Index >= Stk[A + 1]) then
											VIP = Inst[3];
											Stk[A + 3] = Index;
										end
									end
								end
							elseif (Enum <= 62) then
								local ZZZZA = 1;
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + ZZZZA]);
							elseif (Enum > 63) then
								local ZZZZI = 3;
								local ZZZZO = 2;
								Stk[Inst[ZZZZO]] = Stk[Inst[ZZZZI]] - Stk[Inst[4]];
							else
								Stk[Inst[2]] = {};
							end
						end
					elseif (Enum <= 75) then
						local ZZZZN = 69;
						if (Enum <= ZZZZN) then
							if (Enum <= 66) then
								if (Enum == 65) then
									local ZZZZS = 3;
									Stk[Inst[2]] = Stk[Inst[ZZZZS]] - Inst[4];
								else
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								end
							elseif (Enum <= 67) then
								local ZZZZH = 2;
								local A = Inst[ZZZZH];
								local Index = Stk[A];
								local Step = Stk[A + 2];
								if (Step > 0) then
									local ZZZZR = 1;
									if (Index > Stk[A + ZZZZR]) then
										local ZZZZD = 3;
										VIP = Inst[ZZZZD];
									else
										local ZZZZL = 3;
										Stk[A + ZZZZL] = Index;
									end
								elseif (Index < Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							elseif (Enum == 68) then
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								local ZZZZM = 4;
								local ZZZZU = 1;
								local ZZZZC = 3;
								local B = Inst[ZZZZC];
								local K = Stk[B];
								for Idx = B + ZZZZU, Inst[ZZZZM] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
							end
						else
							local ZZZZW = 72;
							if (Enum <= ZZZZW) then
								if (Enum <= 70) then
									local ZZZZG = 3;
									local ZZZZF = 2;
									Stk[Inst[ZZZZF]] = Stk[Inst[ZZZZG]];
								else
									local ZZZZY = 71;
									if (Enum == ZZZZY) then
										local ZZZZB = 2;
										local ZZZZP = 3;
										Upvalues[Inst[ZZZZP]] = Stk[Inst[ZZZZB]];
									else
										local ZZZZK = 4;
										local ZZZZV = 2;
										Stk[Inst[ZZZZV]][Inst[3]] = Inst[ZZZZK];
									end
								end
							elseif (Enum <= 73) then
								local ZZZZJ = 0;
								local ZZZZX = 2;
								local A = Inst[ZZZZX];
								local Index = Stk[A];
								local Step = Stk[A + 2];
								if (Step > ZZZZJ) then
									if (Index > Stk[A + 1]) then
										local ZZZZQ = 3;
										VIP = Inst[ZZZZQ];
									else
										local ZZZZZ = 3;
										Stk[A + ZZZZZ] = Index;
									end
								elseif (Index < Stk[A + 1]) then
									local ZZZZZe = 3;
									VIP = Inst[ZZZZZe];
								else
									local ZZZZZt = 3;
									Stk[A + ZZZZZt] = Index;
								end
							elseif (Enum > 74) then
								local ZZZZZo = 3;
								local ZZZZZa = 2;
								Stk[Inst[ZZZZZa]] = #Stk[Inst[ZZZZZo]];
							else
								local ZZZZZi = 1;
								local A = Inst[2];
								Stk[A](Stk[A + ZZZZZi]);
							end
						end
					else
						local ZZZZZn = 80;
						if (Enum <= ZZZZZn) then
							local ZZZZZs = 77;
							if (Enum <= ZZZZZs) then
								local ZZZZZh = 76;
								if (Enum > ZZZZZh) then
									local ZZZZZr = 3;
									VIP = Inst[ZZZZZr];
								else
									local ZZZZZd = 4;
									if (Stk[Inst[2]] < Inst[ZZZZZd]) then
										local ZZZZZl = 1;
										VIP = VIP + ZZZZZl;
									else
										VIP = Inst[3];
									end
								end
							else
								local ZZZZZc = 78;
								if (Enum <= ZZZZZc) then
									do
										return;
									end
								else
									local ZZZZZu = 79;
									if (Enum == ZZZZZu) then
										local ZZZZZm = 4;
										Stk[Inst[2]] = Stk[Inst[3]] % Inst[ZZZZZm];
									else
										local ZZZZZw = 3;
										local A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[ZZZZZw]));
									end
								end
							end
						elseif (Enum <= 83) then
							local ZZZZZf = 81;
							if (Enum <= ZZZZZf) then
								local ZZZZZg = 4;
								if (Stk[Inst[2]] == Stk[Inst[ZZZZZg]]) then
									local ZZZZZy = 1;
									VIP = VIP + ZZZZZy;
								else
									local ZZZZZp = 3;
									VIP = Inst[ZZZZZp];
								end
							elseif (Enum > 82) then
								local A = Inst[2];
								Stk[A] = Stk[A]();
							else
								local ZZZZZv = 3;
								local ZZZZZb = 2;
								Stk[Inst[ZZZZZb]][Inst[ZZZZZv]] = Inst[4];
							end
						else
							local ZZZZZk = 84;
							if (Enum <= ZZZZZk) then
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Inst[3] do
									Insert(T, Stk[Idx]);
								end
							elseif (Enum == 85) then
								local ZZZZZj = 3;
								local ZZZZZx = 2;
								Stk[Inst[ZZZZZx]] = Inst[ZZZZZj];
							elseif not Stk[Inst[2]] then
								local ZZZZZq = 1;
								VIP = VIP + ZZZZZq;
							else
								VIP = Inst[3];
							end
						end
					end
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
VMCall("LOL!A93O0003083O00496E7374616E63652O033O006E657703093O005363722O656E47756903053O004672616D6503083O005549436F726E657203093O00546578744C6162656C030A3O0055494772616469656E74030A3O005465787442752O746F6E03073O0054657874426F7803043O004E616D6503043O004D656E7503063O00506172656E7403043O0067616D6503073O00506C6179657273030B3O004C6F63616C506C61796572030C3O0057616974466F724368696C6403093O00506C61796572477569030C3O00446973706C61794F72646572026O00F03F030C3O0052657365744F6E537061776E010003103O004261636B67726F756E64436F6C6F723303063O00436F6C6F723303073O0066726F6D524742026O002040030C3O00426F72646572436F6C6F7233026O00494003083O00506F736974696F6E03053O005544696D3202EA6053A07C05D23F028O000295B929808A8CD33F03043O0053697A65025O00608140025O0070734003063O00656E63696D61024A011C207F913DBF025O00802O40030C3O00436F726E657252616469757303043O005544696D026O002440025O00E06F4003163O004261636B67726F756E645472616E73706172656E63790254A244C107CC8EBF0210FCED7F00D1B6BF026O006140026O00424003043O00466F6E7403043O00456E756D03073O00436172742O6F6E03043O005465787403063O006B6179687562030A3O0054657874436F6C6F723303083O005465787453697A65026O003F40023D9DC81F4E58C33F026679F27F3B8FB7BF026O004B40026O00394003063O0041726361646503023O007634026O002C4003053O00436F6C6F72030D3O00436F6C6F7253657175656E636503153O00436F6C6F7253657175656E63654B6579706F696E74025O00405840025O0020624002BB37597F582ACA3F022109E5FFC107AFBF025O00206C4003173O007C20646973636F72642E2O672F726E76622O3870465378026O00324003083O0062746E5F7361697203063O00416374697665025O00804640022C0411609310ED3F025O00804940030B3O004A6F736566696E53616E7303013O0078026O002E4003063O00726F64617065027A7F0FA0D7D6ED3F025O00588140026O003540026O00144003043O006461746102242EB49FE0DA7E3F02DB367A9F2449C23F025O0040814003063O006279206B6179030C3O0063656E74726F5F622O746E73030F3O00426F7264657253697A65506978656C02DB006160CC48A33F02C03EF39F5985C23F025O00A06F40026O006D40026O003040029A5O99B93F020EEA62A0591CD13F02223B07803EB2E43F025O00C05C40025O00804540030C3O00436F707920646973636F7264025O00E06C40025O00A0654002ABDAB29F6C1ACA3F024448E53F070AD93F025O0080624003093O00436865636B204B657903053O006361697861029A5O99D93F02283D43A0498EC93F02D1B1CA1FE835CB3F025O00E06240026O002O4003073O004869676877617903113O00506C616365686F6C646572436F6C6F723303083O006B65792068657265026O005F40025O00C05E40025O00405E40026O00344003063O0073746174757302BC1E1FC0E84AA03F02118933A08DD5EC3F025O00806E4003073O0056697369626C6503083O002A20737461747573026O006940025O00606940025O00806840030B3O00546578745772612O7065642O01030E3O005465787458416C69676E6D656E7403043O004C656674026F634B4060E6CC3F02C292FEFFD2946DBF030A3O004B65792073797374656D030F3O0063656E74726F5F7475746F7269616C02BA11CF3FE54BE03F023D8524FF084DC23F025O0050704002F455BFC016F5C93F02B6B168C0D3946DBF03083O005475746F7269616C03083O007475746F7269616C023CEE631E5CAE8A3F02E12888A0BB3BC23F025O00A06D4003103O00536F7572636553616E734974616C696303163O00312D206A6F696E206F6E2074686520646973636F7264025O00A06440025O00E06440025O00206440026O003340020C06C0405CAE8A3F02856821BF8679CF3F025O00D0704003283O00322D20676F20746F206368617420236B657920616E6420636C69636B206F6E20746865206C696E6B02AA09D5DFA85BD63F031D3O00332D2070612O73207468726F756768207468652073686F7274656E657202C95B781E58AE8A3F023AA9F59FB126DC3F025O00206F40031D3O00342D636F707920616E6420707574206F6E207468652074657874626F780243A028407C3FE13F031D3O00352D636C69636B206F6E2022436865636B204B6579222062752O746F6E03093O00636F726F7574696E6503043O007772617000C1042O0012313O00013O0020075O0002001255000100034O003E3O00020002001231000100013O002007000100010002001255000200044O003E000100020002001231000200013O002007000200020002001255000300044O003E000200020002001231000300013O002007000300030002001255000400054O003E000300020002001231000400013O002007000400040002001255000500064O003E000400020002001231000500013O002007000500050002001255000600064O003E000500020002001231000600013O002007000600060002001255000700074O003E000600020002001231000700013O002007000700070002001255000800064O003E000700020002001231000800013O002007000800080002001255000900084O003E000800020002001231000900013O002007000900090002001255000A00054O003E000900020002001231000A00013O002007000A000A0002001255000B00054O003E000A00020002001231000B00013O002007000B000B0002001255000C00044O003E000B00020002001231000C00013O002007000C000C0002001255000D00054O003E000C00020002001231000D00013O002007000D000D0002001255000E00064O003E000D00020002001231000E00013O002007000E000E0002001255000F00044O003E000E00020002001231000F00013O002007000F000F0002001255001000084O003E000F00020002001231001000013O002007001000100002001255001100054O003E001000020002001231001100013O002007001100110002001255001200074O003E001100020002001231001200013O002007001200120002001255001300084O003E001200020002001231001300013O002007001300130002001255001400054O003E001300020002001231001400013O002007001400140002001255001500074O003E001400020002001231001500013O002007001500150002001255001600094O003E001500020002001231001600013O002007001600160002001255001700054O003E001600020002001231001700013O002007001700170002001255001800074O003E001700020002001231001800013O002007001800180002001255001900064O003E001800020002001231001900013O002007001900190002001255001A00054O003E001900020002001231001A00013O002007001A001A0002001255001B00064O003E001A00020002001231001B00013O002007001B001B0002001255001C00044O003E001B00020002001231001C00013O002007001C001C0002001255001D00054O003E001C00020002001231001D00013O002007001D001D0002001255001E00064O003E001D00020002001231001E00013O002007001E001E0002001255001F00064O003E001E00020002001231001F00013O002007001F001F0002001255002000064O003E001F00020002001231002000013O002007002000200002001255002100064O003E002000020002001231002100013O002007002100210002001255002200064O003E002100020002001231002200013O002007002200220002001255002300064O003E0022000200020030523O000A000B0012310023000D3O00200700230023000E00200700230023000F002009002300230010001255002500114O000C00230025000200100D3O000C00230030523O001200130030523O0014001500100D0001000C3O001231002300173O002007002300230018001255002400193O001255002500193O001255002600194O000C00230026000200100D000100160023001231002300173O0020070023002300180012550024001B3O0012550025001B3O0012550026001B4O000C00230026000200100D0001001A00230012310023001D3O0020070023002300020012550024001E3O0012550025001F3O001255002600203O0012550027001F4O000C00230027000200100D0001001C00230012310023001D3O0020070023002300020012550024001F3O001255002500223O0012550026001F3O001255002700234O000C00230027000200100D0001002100230030520002000A002400100D0002000C0001001231002300173O0020070023002300180012550024001F3O0012550025001F3O0012550026001F4O000C00230026000200100D000200160023001231002300173O0020070023002300180012550024001B3O0012550025001B3O0012550026001B4O000C00230026000200100D0002001A00230012310023001D3O002007002300230002001255002400253O0012550025001F3O0012550026001F3O0012550027001F4O000C00230027000200100D0002001C00230012310023001D3O0020070023002300020012550024001F3O001255002500223O0012550026001F3O001255002700264O000C00230027000200100D000200210023001231002300283O0020070023002300020012550024001F3O001255002500294O000C00230025000200100D00030027002300100D0003000C000200100D0004000C0002001231002300173O0020070023002300180012550024002A3O0012550025002A3O0012550026002A4O000C00230026000200100D0004001600230030520004002B00130012310023001D3O0020070023002300020012550024002C3O0012550025001F3O0012550026002D3O0012550027001F4O000C00230027000200100D0004001C00230012310023001D3O0020070023002300020012550024001F3O0012550025002E3O0012550026001F3O0012550027002F4O000C00230027000200100D000400210023001231002300313O00200700230023003000200700230023003200100D000400300023003052000400330034001231002300173O0020070023002300180012550024002A3O0012550025002A3O0012550026002A4O000C00230026000200100D00040035002300305200040036003700100D0005000C0002001231002300173O0020070023002300180012550024002A3O0012550025002A3O0012550026002A4O000C00230026000200100D0005001600230030520005002B00130012310023001D3O002007002300230002001255002400383O0012550025001F3O001255002600393O0012550027001F4O000C00230027000200100D0005001C00230012310023001D3O0020070023002300020012550024001F3O0012550025003A3O0012550026001F3O0012550027003B4O000C00230027000200100D000500210023001231002300313O00200700230023003000200700230023003C00100D00050030002300305200050033003D001231002300173O0020070023002300180012550024002A3O0012550025002A3O0012550026002A4O000C00230026000200100D00050035002300305200050036003E001231002300403O0020070023002300022O003F002400013O001231002500413O0020070025002500020012550026001F3O001231002700173O002007002700270018001255002800423O0012550029001F3O001255002A00434O00350027002A4O001000253O0002001231002600413O002007002600260002001255002700133O001231002800173O002007002800280018001255002900423O001255002A001F3O001255002B00434O00350028002B4O001600266O001800243O00012O003E00230002000200100D0006003F002300100D0006000C000200100D0007000C0002001231002300173O0020070023002300180012550024002A3O0012550025002A3O0012550026002A4O000C00230026000200100D0007001600230030520007002B00130012310023001D3O002007002300230002001255002400443O0012550025001F3O001255002600453O0012550027001F4O000C00230027000200100D0007001C00230012310023001D3O0020070023002300020012550024001F3O001255002500463O0012550026001F3O0012550027002F4O000C00230027000200100D000700210023001231002300313O00200700230023003000200700230023003200100D000700300023003052000700330047001231002300173O0020070023002300180012550024002A3O0012550025002A3O0012550026002A4O000C00230026000200100D0007003500230030520007003600480030520008000A004900100D0008000C00020030520008004A0015001231002300173O0020070023002300180012550024003B3O0012550025003B3O0012550026003B4O000C00230026000200100D0008001600230030520008002B0013001231002300173O0020070023002300180012550024004B3O0012550025004B3O0012550026004B4O000C00230026000200100D0008001A00230012310023001D3O0020070023002300020012550024004C3O0012550025001F3O001255002600453O0012550027001F4O000C00230027000200100D0008001C00230012310023001D3O0020070023002300020012550024001F3O0012550025004D3O0012550026001F3O001255002700264O000C00230027000200100D000800210023001231002300313O00200700230023003000200700230023004E00100D00080030002300305200080033004F001231002300173O0020070023002300180012550024002A3O0012550025002A3O0012550026002A4O000C00230026000200100D00080035002300305200080036003B001231002300283O0020070023002300020012550024001F3O001255002500504O000C00230025000200100D00090027002300100D0009000C0008001231002300283O0020070023002300020012550024001F3O001255002500294O000C00230025000200100D000A0027002300100D000A000C0001003052000B000A005100100D000B000C0001001231002300173O0020070023002300180012550024001F3O0012550025001F3O0012550026001F4O000C00230026000200100D000B001600230012310023001D3O0020070023002300020012550024001F3O0012550025001F3O001255002600523O0012550027001F4O000C00230027000200100D000B001C00230012310023001D3O0020070023002300020012550024001F3O001255002500533O0012550026001F3O001255002700544O000C00230027000200100D000B00210023001231002300283O0020070023002300020012550024001F3O001255002500554O000C00230025000200100D000C0027002300100D000C000C000B003052000D000A005600100D000D000C000B001231002300173O0020070023002300180012550024002A3O0012550025002A3O0012550026002A4O000C00230026000200100D000D00160023003052000D002B00130012310023001D3O002007002300230002001255002400573O0012550025001F3O001255002600583O0012550027001F4O000C00230027000200100D000D001C00230012310023001D3O0020070023002300020012550024001F3O001255002500593O0012550026001F3O001255002700484O000C00230027000200100D000D00210023001231002300313O00200700230023003000200700230023003200100D000D00300023003052000D0033005A001231002300173O0020070023002300180012550024002A3O0012550025002A3O0012550026002A4O000C00230026000200100D000D00350023003052000D0036003E003052000E000A005B00100D000E000C0001001231002300173O0020070023002300180012550024001F3O0012550025001F3O0012550026001F4O000C00230026000200100D000E00160023001231002300173O0020070023002300180012550024001F3O0012550025001F3O0012550026001F4O000C00230026000200100D000E001A0023003052000E005C001F0012310023001D3O0020070023002300020012550024005D3O0012550025001F3O0012550026005E3O0012550027001F4O000C00230027000200100D000E001C00230012310023001D3O0020070023002300020012550024001F3O0012550025005F3O0012550026001F3O001255002700604O000C00230027000200100D000E0021002300100D000F000C000E001231002300173O002007002300230018001255002400613O001255002500613O001255002600614O000C00230026000200100D000F00160023003052000F002B0062001231002300173O0020070023002300180012550024004B3O0012550025004B3O0012550026004B4O000C00230026000200100D000F001A00230012310023001D3O002007002300230002001255002400633O0012550025001F3O001255002600643O0012550027001F4O000C00230027000200100D000F001C00230012310023001D3O0020070023002300020012550024001F3O001255002500653O0012550026001F3O001255002700664O000C00230027000200100D000F00210023001231002300313O00200700230023003000200700230023003200100D000F00300023003052000F00330067001231002300173O002007002300230018001255002400683O001255002500683O001255002600684O000C00230026000200100D000F00350023003052000F0036003E001231002300283O0020070023002300020012550024001F3O001255002500504O000C00230025000200100D00100027002300100D0010000C000F001231002300403O0020070023002300022O003F002400013O001231002500413O0020070025002500020012550026001F3O001231002700173O002007002700270018001255002800693O001255002900693O001255002A00694O00350027002A4O001000253O0002001231002600413O002007002600260002001255002700133O001231002800173O002007002800280018001255002900693O001255002A00693O001255002B00694O00350028002B4O001600266O001800243O00012O003E00230002000200100D0011003F002300100D0011000C000F00100D0012000C000E001231002300173O002007002300230018001255002400613O001255002500613O001255002600614O000C00230026000200100D0012001600230030520012002B0062001231002300173O0020070023002300180012550024004B3O0012550025004B3O0012550026004B4O000C00230026000200100D0012001A00230012310023001D3O0020070023002300020012550024006A3O0012550025001F3O0012550026006B3O0012550027001F4O000C00230027000200100D0012001C00230012310023001D3O0020070023002300020012550024001F3O0012550025006C3O0012550026001F3O0012550027001B4O000C00230027000200100D001200210023001231002300313O00200700230023003000200700230023003200100D00120030002300305200120033006D001231002300173O002007002300230018001255002400683O001255002500683O001255002600684O000C00230026000200100D00120035002300305200120036003E001231002300283O0020070023002300020012550024001F3O001255002500504O000C00230025000200100D00130027002300100D0013000C0012001231002300403O0020070023002300022O003F002400013O001231002500413O0020070025002500020012550026001F3O001231002700173O002007002700270018001255002800693O001255002900693O001255002A00694O00350027002A4O001000253O0002001231002600413O002007002600260002001255002700133O001231002800173O002007002800280018001255002900693O001255002A00693O001255002B00694O00350028002B4O001600266O001800243O00012O003E00230002000200100D0014003F002300100D0014000C00120030520015000A006E00100D0015000C000E001231002300173O002007002300230018001255002400613O001255002500613O001255002600614O000C00230026000200100D0015001600230030520015002B006F0030520015005C001F0012310023001D3O002007002300230002001255002400703O0012550025001F3O001255002600713O0012550027001F4O000C00230027000200100D0015001C00230012310023001D3O0020070023002300020012550024001F3O001255002500723O0012550026001F3O001255002700734O000C00230027000200100D001500210023001231002300313O00200700230023003000200700230023007400100D001500300023001231002300173O002007002300230018001255002400683O001255002500683O001255002600684O000C00230026000200100D001500750023003052001500330076001231002300173O002007002300230018001255002400773O001255002500783O001255002600794O000C00230026000200100D00150035002300305200150036003E001231002300283O0020070023002300020012550024001F3O0012550025007A4O000C00230025000200100D00160027002300100D0016000C0015001231002300403O0020070023002300022O003F002400013O001231002500413O0020070025002500020012550026001F3O001231002700173O002007002700270018001255002800693O001255002900693O001255002A00694O00350027002A4O001000253O0002001231002600413O002007002600260002001255002700133O001231002800173O002007002800280018001255002900693O001255002A00693O001255002B00694O00350028002B4O001600266O001800243O00012O003E00230002000200100D0017003F002300100D0017000C00150030520018000A007B00100D0018000C000E001231002300173O0020070023002300180012550024002A3O0012550025002A3O0012550026002A4O000C00230026000200100D0018001600230030520018002B00130012310023001D3O0020070023002300020012550024007C3O0012550025001F3O0012550026007D3O0012550027001F4O000C00230027000200100D0018001C00230012310023001D3O0020070023002300020012550024001F3O0012550025007E3O0012550026001F3O001255002700614O000C00230027000200100D0018002100230030520018007F0015001231002300313O00200700230023003000200700230023004E00100D001800300023003052001800330080001231002300173O002007002300230018001255002400813O001255002500823O001255002600834O000C00230026000200100D001800350023003052001800360050003052001800840085001231002300313O00200700230023008600200700230023008700100D001800860023001231002300283O0020070023002300020012550024001F3O001255002500504O000C00230025000200100D00190027002300100D0019000C000E00100D001A000C000E001231002300173O0020070023002300180012550024002A3O0012550025002A3O0012550026002A4O000C00230026000200100D001A00160023003052001A002B00130012310023001D3O002007002300230002001255002400883O0012550025001F3O001255002600893O0012550027001F4O000C00230027000200100D001A001C00230012310023001D3O0020070023002300020012550024001F3O0012550025002E3O0012550026001F3O0012550027002F4O000C00230027000200100D001A00210023001231002300313O00200700230023003000200700230023003200100D001A00300023003052001A0033008A001231002300173O0020070023002300180012550024002A3O0012550025002A3O0012550026002A4O000C00230026000200100D001A00350023003052001A00360037003052001B000A008B00100D001B000C0001001231002300173O0020070023002300180012550024001F3O0012550025001F3O0012550026001F4O000C00230026000200100D001B00160023001231002300173O0020070023002300180012550024001F3O0012550025001F3O0012550026001F4O000C00230026000200100D001B001A0023003052001B005C001F0012310023001D3O0020070023002300020012550024008C3O0012550025001F3O0012550026008D3O0012550027001F4O000C00230027000200100D001B001C00230012310023001D3O0020070023002300020012550024001F3O0012550025008E3O0012550026001F3O001255002700604O000C00230027000200100D001B00210023001231002300283O0020070023002300020012550024001F3O001255002500504O000C00230025000200100D001C0027002300100D001C000C001B00100D001D000C001B001231002300173O0020070023002300180012550024002A3O0012550025002A3O0012550026002A4O000C00230026000200100D001D00160023003052001D002B00130012310023001D3O0020070023002300020012550024008F3O0012550025001F3O001255002600903O0012550027001F4O000C00230027000200100D001D001C00230012310023001D3O0020070023002300020012550024001F3O0012550025002E3O0012550026001F3O0012550027002F4O000C00230027000200100D001D00210023001231002300313O00200700230023003000200700230023003200100D001D00300023003052001D00330091001231002300173O0020070023002300180012550024002A3O0012550025002A3O0012550026002A4O000C00230026000200100D001D00350023003052001D00360037003052001E000A009200100D001E000C001B001231002300173O0020070023002300180012550024002A3O0012550025002A3O0012550026002A4O000C00230026000200100D001E00160023003052001E002B00130012310023001D3O002007002300230002001255002400933O0012550025001F3O001255002600943O0012550027001F4O000C00230027000200100D001E001C00230012310023001D3O0020070023002300020012550024001F3O001255002500953O0012550026001F3O001255002700614O000C00230027000200100D001E00210023001231002300313O00200700230023003000200700230023009600100D001E00300023003052001E00330097001231002300173O002007002300230018001255002400983O001255002500993O0012550026009A4O000C00230026000200100D001E00350023003052001E0036009B003052001E00840085001231002300313O00200700230023008600200700230023008700100D001E00860023003052001F000A009200100D001F000C001B001231002300173O0020070023002300180012550024002A3O0012550025002A3O0012550026002A4O000C00230026000200100D001F00160023003052001F002B00130012310023001D3O0020070023002300020012550024009C3O0012550025001F3O0012550026009D3O0012550027001F4O000C00230027000200100D001F001C00230012310023001D3O0020070023002300020012550024001F3O0012550025009E3O0012550026001F3O001255002700614O000C00230027000200100D001F00210023001231002300313O00200700230023003000200700230023009600100D001F00300023003052001F0033009F001231002300173O002007002300230018001255002400983O001255002500993O0012550026009A4O000C00230026000200100D001F00350023003052001F0036009B003052001F00840085001231002300313O00200700230023008600200700230023008700100D001F008600230030520020000A009200100D0020000C001B001231002300173O0020070023002300180012550024002A3O0012550025002A3O0012550026002A4O000C00230026000200100D0020001600230030520020002B00130012310023001D3O002007002300230002001255002400933O0012550025001F3O001255002600A03O0012550027001F4O000C00230027000200100D0020001C00230012310023001D3O0020070023002300020012550024001F3O0012550025009E3O0012550026001F3O001255002700614O000C00230027000200100D002000210023001231002300313O00200700230023003000200700230023009600100D0020003000230030520020003300A1001231002300173O002007002300230018001255002400983O001255002500993O0012550026009A4O000C00230026000200100D00200035002300305200200036009B003052002000840085001231002300313O00200700230023008600200700230023008700100D0020008600230030520021000A009200100D0021000C001B001231002300173O0020070023002300180012550024002A3O0012550025002A3O0012550026002A4O000C00230026000200100D0021001600230030520021002B00130012310023001D3O002007002300230002001255002400A23O0012550025001F3O001255002600A33O0012550027001F4O000C00230027000200100D0021001C00230012310023001D3O0020070023002300020012550024001F3O001255002500A43O0012550026001F3O001255002700614O000C00230027000200100D002100210023001231002300313O00200700230023003000200700230023009600100D0021003000230030520021003300A5001231002300173O002007002300230018001255002400983O001255002500993O0012550026009A4O000C00230026000200100D00210035002300305200210036009B003052002100840085001231002300313O00200700230023008600200700230023008700100D0021008600230030520022000A009200100D0022000C001B001231002300173O0020070023002300180012550024002A3O0012550025002A3O0012550026002A4O000C00230026000200100D0022001600230030520022002B00130012310023001D3O002007002300230002001255002400A23O0012550025001F3O001255002600A63O0012550027001F4O000C00230027000200100D0022001C00230012310023001D3O0020070023002300020012550024001F3O001255002500A43O0012550026001F3O001255002700614O000C00230027000200100D002200210023001231002300313O00200700230023003000200700230023009600100D0022003000230030520022003300A7001231002300173O002007002300230018001255002400983O001255002500993O0012550026009A4O000C00230026000200100D00220035002300305200220036009B003052002200840085001231002300313O00200700230023008600200700230023008700100D00220086002300061F00233O000100012O00343O00023O001231002400A83O0020070024002400A92O0046002500234O003E0024000200022O000500240001000100061F00240001000100012O00343O00083O001231002500A83O0020070025002500A92O0046002600244O003E0025000200022O000500250001000100061F00250002000100012O00343O00013O001231002600A83O0020070026002600A92O0046002700254O003E0026000200022O000500260001000100061F00260003000100012O00343O00013O001231002700A83O0020070027002700A92O0046002800264O003E0027000200022O000500270001000100061F00270004000100012O00343O000B3O001231002800A83O0020070028002800A92O0046002900274O003E0028000200022O000500280001000100061F00280005000100012O00343O000F3O001231002900A83O0020070029002900A92O0046002A00284O003E0029000200022O000500290001000100061F00290006000100012O00343O00123O001231002A00A83O002007002A002A00A92O0046002B00294O003E002A000200022O0005002A0001000100061F002A0007000100012O00347O001231002B00A83O002007002B002B00A92O0046002C002A4O003E002B000200022O0005002B0001000100061F002B0008000100012O00347O001231002C00A83O002007002C002C00A92O0046002D002B4O003E002C000200022O0005002C000100012O003A3O00013O00093O00123O0003083O00496E7374616E63652O033O006E6577030B3O004C6F63616C53637269707403043O0067616D65030A3O0047657453657276696365030C3O0054772O656E5365727669636503063O00506172656E7403163O004261636B67726F756E645472616E73706172656E6379026O00F03F03093O0054772O656E496E666F03043O00456E756D030B3O00456173696E675374796C6503063O004C696E656172030F3O00456173696E67446972656374696F6E03053O00496E4F757403063O00437265617465028O0003043O00506C6179001E3O0012313O00013O0020075O0002001255000100034O000E00026O000C3O00020002001231000100043O002009000100010005001255000300064O000C00010003000200200700023O00070030520002000800090012310003000A3O002007000300030002001255000400093O0012310005000B3O00200700050005000C00200700050005000D0012310006000B3O00200700060006000E00200700060006000F2O000C0003000600020020090004000100102O0046000600024O0046000700034O003F00083O00010030520008000800112O000C0004000800020020090005000400122O004A0005000200012O003A3O00017O000A3O0003083O00496E7374616E63652O033O006E6577030B3O004C6F63616C53637269707403063O00506172656E7403053O004672616D6503043O0067616D65030A3O0047657453657276696365030C3O0054772O656E5365727669636503103O004D6F75736542752O746F6E31446F776E03073O00436F2O6E65637400163O0012313O00013O0020075O0002001255000100034O000E00026O000C3O0002000200200700013O000400200700010001000400200700010001000400200700010001000400200700010001000500200700023O0004001231000300063O002009000300030007001255000500084O000C00030005000200200700040002000900200900040004000A00061F00063O000100022O00343O00034O00343O00014O00500004000600012O003A3O00013O00013O000D3O0003093O0054772O656E496E666F2O033O006E6577026O00F03F03043O00456E756D030B3O00456173696E675374796C6503063O004C696E656172030F3O00456173696E67446972656374696F6E2O033O004F757403063O0043726561746503163O004261636B67726F756E645472616E73706172656E637903043O00506C617903073O0056697369626C65012O00163O0012313O00013O0020075O0002001255000100033O001231000200043O002007000200020005002007000200020006001231000300043O0020070003000300070020070003000300082O000C3O000300022O000E00015O0020090001000100092O000E000300014O004600046O003F00053O00010030520005000A00032O000C00010005000200200900020001000B2O004A0002000200012O000E000200013O0030520002000C000D2O003A3O00017O00123O0003083O00496E7374616E63652O033O006E6577030B3O004C6F63616C53637269707403043O0067616D65030A3O0047657453657276696365030C3O0054772O656E5365727669636503063O00506172656E7403163O004261636B67726F756E645472616E73706172656E6379026O00F03F03093O0054772O656E496E666F03043O00456E756D030B3O00456173696E675374796C6503063O004C696E656172030F3O00456173696E67446972656374696F6E03053O00496E4F757403063O00437265617465028O0003043O00506C6179001E3O0012313O00013O0020075O0002001255000100034O000E00026O000C3O00020002001231000100043O002009000100010005001255000300064O000C00010003000200200700023O00070030520002000800090012310003000A3O002007000300030002001255000400093O0012310005000B3O00200700050005000C00200700050005000D0012310006000B3O00200700060006000E00200700060006000F2O000C0003000600020020090004000100102O0046000600024O0046000700034O003F00083O00010030520008000800112O000C0004000800020020090005000400122O004A0005000200012O003A3O00017O00213O0003083O00496E7374616E63652O033O006E6577030B3O004C6F63616C536372697074030A3O006C6F6164737472696E6703043O0067616D6503073O00482O747047657403423O00682O7470733A2O2F7261772E67697468756275736572636F6E74656E742E636F6D2F426F6375734C756B652F55492F6D61696E2F5354582F4D6F64756C652E4C756103423O00682O7470733A2O2F7261772E67697468756275736572636F6E74656E742E636F6D2F426F6375734C756B652F55492F6D61696E2F5354582F436C69656E742E4C756103093O005363722O656E47756903063O00506172656E7403073O00436F7265477569030E3O005A496E6465784265686176696F7203043O00456E756D03073O005369626C696E6703063O004E6F7469667903053O005469746C65030D3O006B6179687562206C6F61646572030B3O004465736372697074696F6E03273O00646F20796F752077616E7420746F20732O65207468652073752O706F727465642067616D65733F030C3O004F75746C696E65436F6C6F7203063O00436F6C6F723303073O0066726F6D524742026O00544003043O0054696D65026O00344003043O005479706503063O006F7074696F6E03053O00496D616765032A3O00682O74703A2O2F3O772E726F626C6F782E636F6D2F612O7365742F3F69643D36303233343236393233030A3O00496D616765436F6C6F72025O00E06F40026O00554003083O0043612O6C6261636B00383O0012313O00013O0020075O0002001255000100034O000E00026O000C3O00020002001231000100043O001231000200053O002009000200020006001255000400074O0035000200044O001000013O00022O0032000100010002001231000200043O001231000300053O002009000300030006001255000500084O0035000300054O001000023O00022O0032000200010002001231000300093O001231000400053O00200700040004000B00100D0003000A0004001231000300093O0012310004000D3O00200700040004000C00200700040004000E00100D0003000C000400200900030002000F2O003F00053O00020030520005001000110030520005001200132O003F00063O0003001231000700153O002007000700070016001255000800173O001255000900173O001255000A00174O000C0007000A000200100D0006001400070030520006001800190030520006001A001B2O003F00073O00030030520007001C001D001231000800153O0020070008000800160012550009001F3O001255000A00203O001255000B00204O000C0008000B000200100D0007001E000800061F00083O000100012O00343O00023O00100D0007002100082O00500003000700012O003A3O00013O00013O000E3O002O0103063O004E6F7469667903053O005469746C65030F3O0053752O706F727465642067616D6573030B3O004465736372697074696F6E03183O004B727573685076500A4B41540A526F6775652044656D6F6E030C3O004F75746C696E65436F6C6F7203063O00436F6C6F723303073O0066726F6D524742026O00544003043O0054696D65026O00144003043O005479706503073O0064656661756C7401133O00261E3O0012000100010004083O001200012O000E00015O0020090001000100022O003F00033O00020030520003000300040030520003000500062O003F00043O0003001231000500083O0020070005000500090012550006000A3O0012550007000A3O0012550008000A4O000C00050008000200100D0004000700050030520004000B000C0030520004000D000E2O00500001000400012O003A3O00017O00193O0003083O00496E7374616E63652O033O006E6577030B3O004C6F63616C536372697074026O00F03F03063O00506172656E7403043O006461746103023O005F4703093O006C2O6F705F646174612O0103023O006F7303043O00646174652O033O00212A7403043O00686F7572026O003840026O00284003023O00414D03023O00504D03063O00737472696E6703063O00666F726D6174030C3O00253032693A253032692025732O033O006D696E03043O005465787403143O007O207C6O206279206B617903043O0077616974026O00F83F00293O0012313O00013O0020075O0002001255000100034O000E00026O000C3O00020002001255000100043O00200700023O0005002007000200020006001231000300073O0030520003000800090012310003000A3O00200700030003000B0012550004000C4O003E00030002000200200700040003000D2O001B00040004000100204F00040004000E00264C000400160001000F0004083O00160001001255000500103O00062100050017000100010004083O00170001001255000500113O001231000600123O002007000600060013001255000700143O00201C00080004000400204F00080008000F0020110008000800040020070009000300152O0046000A00054O000C0006000A00022O0046000700063O001255000800174O004500070007000800100D000200160007001231000700183O001255000800194O004A0007000200010004083O000A00012O003A3O00017O000B3O0003083O00496E7374616E63652O033O006E6577030B3O004C6F63616C53637269707403063O00506172656E74030A3O006C6F6164737472696E6703043O0067616D6503073O00482O747047657403423O00682O7470733A2O2F7261772E67697468756275736572636F6E74656E742E636F6D2F426F6375734C756B652F55492F6D61696E2F5354582F4D6F64756C652E4C756103423O00682O7470733A2O2F7261772E67697468756275736572636F6E74656E742E636F6D2F426F6375734C756B652F55492F6D61696E2F5354582F436C69656E742E4C756103103O004D6F75736542752O746F6E31446F776E03073O00436F2O6E656374001A3O0012313O00013O0020075O0002001255000100034O000E00026O000C3O0002000200200700013O0004001231000200053O001231000300063O002009000300030007001255000500084O0035000300054O001000023O00022O0032000200010002001231000300053O001231000400063O002009000400040007001255000600094O0035000400064O001000033O00022O003200030001000200200700040001000A00200900040004000B00061F00063O000100012O00343O00034O00500004000600012O003A3O00013O00013O000F3O00030C3O00736574636C6970626F617264031D3O00682O7470733A2O2F646973636F72642E2O672F726E76622O387046537803063O004E6F7469667903053O005469746C6503073O0053752O63652O73030B3O004465736372697074696F6E03273O00746865206C696E6B206F662074686520646973636F72642068617320622O656E20636F70696564030C3O004F75746C696E65436F6C6F7203063O00436F6C6F723303073O0066726F6D524742026O00544003043O0054696D65026O00144003043O005479706503073O0064656661756C7400143O0012313O00013O001255000100024O004A3O000200012O000E7O0020095O00032O003F00023O00020030520002000400050030520002000600072O003F00033O0003001231000400093O00200700040004000A0012550005000B3O0012550006000B3O0012550007000B4O000C00040007000200100D0003000800040030520003000C000D0030520003000E000F2O00503O000300012O003A3O00017O00103O0003083O00496E7374616E63652O033O006E6577030B3O004C6F63616C53637269707403043O0067616D6503073O00482O747047657403213O00682O7470733A2O2F706173746562696E2E636F6D2F7261772F6743584B69457A6D03073O00506C616365496403063O00506172656E7403063O0073746174757303053O004672616D6503093O0036322O313239373630030A3O00382O302O373631323738030A3O003931303338392O38323803413O00682O7470733A2O2F7261772E67697468756275736572636F6E74656E742E636F6D2F7476677565696D657238342F6A7368642O68666B61796875622F6D61696E2F03113O004D6F75736542752O746F6E31436C69636B03073O00436F2O6E65637400283O0012313O00013O0020075O0002001255000100034O000E00026O000C3O00020002001231000100043O002009000100010005001255000300064O000C000100030002001231000200043O00200700020002000700200700033O000800200700030003000800200700030003000900200700043O000800200700040004000800200700040004000800200700040004000800200700040004000A2O000300056O003F000600033O0012550007000B3O0012550008000C3O0012550009000D4O00330006000300010012550007000E3O00200700083O000800200700080008000F00200900080008001000061F000A3O000100082O00348O00343O00014O00343O00064O00343O00024O00343O00054O00343O00034O00343O00044O00343O00074O00500008000A00012O003A3O00013O00013O00173O0003063O00506172656E7403053O00636169786103043O005465787403063O0069706169727303083O00746F737472696E6703073O0056697369626C652O01031D3O00737563652O7321206C6F6164696E6720746865207363726970743O2E026O00F03F03063O00737472696E672O033O0073756203043O0077616974027O00400100030A3O006C6F6164737472696E6703043O0067616D6503073O00482O747047657403043O002E6C756103073O00506C6179657273030B3O004C6F63616C506C6179657203043O004B69636B03253O006B6179687562206973206E6F742073752O706F72746564206F6E20746869732067616D652103163O002A2077726F6E67206F722065787069726564206B657900594O000E7O0020075O00010020075O00010020075O00020020075O00032O000E000100013O0006513O0041000100010004083O00410001001231000100044O000E000200024O00260001000200030004083O00350001001231000600054O000E000700034O003E00060002000200065100050035000100060004083O003500012O0003000600014O0047000600044O000E000600053O003052000600060007001255000600083O001255000700094O004B000800063O001255000900093O0004490007002500012O000E000B00053O001231000C000A3O002007000C000C000B2O0046000D00063O001255000E00094O0046000F000A4O000C000C000F000200100D000B0003000C001231000B000C4O0005000B0001000100043C0007001A00010012310007000C3O0012550008000D4O004A0007000200012O000E000700063O00305200070006000E0012310007000F3O001231000800103O0020090008000800112O000E000A00074O000E000B00033O001255000C00124O0045000A000A000C2O00350008000A4O001000073O00022O00050007000100010004083O003700010006270001000C000100020004083O000C00012O000E000100043O00062100010058000100010004083O00580001001231000100103O002007000100010013002007000100010014002009000100010015001255000300164O00500001000300010004083O005800012O000E000100053O003052000100060007001255000100173O001255000200094O004B000300013O001255000400093O0004490002005300012O000E000600053O0012310007000A3O00200700070007000B2O0046000800013O001255000900094O0046000A00054O000C0007000A000200100D0006000300070012310006000C4O000500060001000100043C0002004800010012310002000C3O001255000300094O004A0002000200012O000E000200053O00305200020006000E2O003A3O00017O000B3O0003083O00496E7374616E63652O033O006E6577030B3O004C6F63616C53637269707403043O0067616D65030A3O004765745365727669636503103O0055736572496E7075745365727669636503063O00506172656E7403053O004672616D65030A3O00496E707574426567616E03073O00436F2O6E656374030C3O00496E7075744368616E67656400253O0012313O00013O0020075O0002001255000100034O000E00026O000C3O00020002001231000100043O002009000100010005001255000300064O000C00010003000200200700023O00070020070002000200082O002B000300063O00061F00073O000100032O00343O00054O00343O00024O00343O00063O00200700080002000900200900080008000A00061F000A0001000100042O00343O00034O00343O00054O00343O00064O00343O00024O00500008000A000100200700080002000B00200900080008000A00061F000A0002000100012O00343O00044O00500008000A000100200700080001000B00200900080008000A00061F000A0003000100032O00343O00044O00343O00034O00343O00074O00500008000A00012O003A3O00013O00043O00073O0003083O00506F736974696F6E03053O005544696D322O033O006E657703013O005803053O005363616C6503063O004F2O6673657403013O005901193O00200700013O00012O000E00026O00400001000100022O000E000200013O001231000300023O0020070003000300032O000E000400023O0020070004000400040020070004000400052O000E000500023O0020070005000500040020070005000500060020070006000100042O001B0005000500062O000E000600023O0020070006000600070020070006000600052O000E000700023O0020070007000700070020070007000700060020070008000100072O001B0007000700082O000C00030007000200100D0002000100032O003A3O00017O00073O00030D3O0055736572496E7075745479706503043O00456E756D030C3O004D6F75736542752O746F6E3103053O00546F75636803083O00506F736974696F6E03073O004368616E67656403073O00436F2O6E656374011A3O00200700013O0001001231000200023O0020070002000200010020070002000200030006220001000C000100020004083O000C000100200700013O0001001231000200023O00200700020002000100200700020002000400065100010019000100020004083O001900012O0003000100014O004700015O00200700013O00052O0047000100014O000E000100033O0020070001000100052O0047000100023O00200700013O000600200900010001000700061F00033O000100022O00348O001A8O00500001000300012O003A3O00013O00013O00033O00030E3O0055736572496E707574537461746503043O00456E756D2O033O00456E64000A4O000E7O0020075O0001001231000100023O0020070001000100010020070001000100030006513O0009000100010004083O000900012O00038O00473O00014O003A3O00017O00043O00030D3O0055736572496E7075745479706503043O00456E756D030D3O004D6F7573654D6F76656D656E7403053O00546F756368010E3O00200700013O0001001231000200023O0020070002000200010020070002000200030006220001000C000100020004083O000C000100200700013O0001001231000200023O0020070002000200010020070002000200040006510001000D000100020004083O000D00012O00478O003A3O00019O002O00010A4O000E00015O0006513O0009000100010004083O000900012O000E000100013O0006140001000900013O0004083O000900012O000E000100024O004600026O004A0001000200012O003A3O00017O00063O0003083O00496E7374616E63652O033O006E6577030B3O004C6F63616C53637269707403063O00506172656E74030C3O00446973706C61794F72646572025O0088C34000083O0012313O00013O0020075O0002001255000100034O000E00026O000C3O0002000200200700013O00040030520001000500062O003A3O00017O00", GetFEnv(), ...);
