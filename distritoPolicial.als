module delegacia

abstract sig Ocorrencia {
	AtendidoPor: set Policial
}

sig Delegacia{
	Folga: set Agente
}

sig Branco extends Ocorrencia {
}

sig Verde extends Ocorrencia {
}

sig Azul extends Ocorrencia {
}

sig Vermelho extends Ocorrencia {
	Investigacao: set Detetive
}

abstract sig Agente{}
abstract sig Policial extends Agente{}
abstract sig Exp extends Policial{}
sig Detetive extends Agente{}
sig Xerife extends Exp{}
sig Veterano extends Exp{}
sig Novato extends Policial{}

-- Avisa se o policial está atendendo a ocorrencia em questão
pred atende[p:Policial,o:Ocorrencia] {
	p in o.AtendidoPor
}
-- Avisa se o policial está de prontidão, isto é, na delegacia
pred prontidao[a:Agente,d:Delegacia] {
	a in d.Folga
}

--Avisa se o Detetive está atendendo um código vermelho em questão
pred investigando[d:Detetive,v:Vermelho] {
	d in v.Investigacao
}

fact {
	#(Delegacia) = 1
	
	--Cada funcionario deve estar na delegecia (disponível) ou trabalhando em um caso, nunca associado aos dois ao mesmo tempo!
	all p:Policial | (one p.~AtendidoPor and no p.~Folga) or (no p.~AtendidoPor and one p.~Folga)
	all d:Detetive | (one d.~Investigacao and no d.~Folga) or (no d.~Investigacao and one d.~Folga)
	
	-- Quantidade de policiais e detetives para cada caso
	all v:Vermelho | #(v.AtendidoPor) = 4 and #(v.Investigacao) = 1
	all a:Azul | #(a.AtendidoPor) = 4
	all b:Branco | #(b.AtendidoPor) = 1 or #(b.AtendidoPor) = 2
	all d:Verde | #(d.AtendidoPor) = 2 or #(d.AtendidoPor) = 3

	-- Nenhum novato deve ir para a ocorrência sem a presença de um experiente (Policial Veterano ou Xerife)
	all n:Novato,o:Ocorrencia | atende[n,o] => some e:Exp | atende[e,o]
	
	-- O Xerife só atua quando for o último policial disponível
	all v:Veterano,x:Xerife,d:Delegacia | prontidao[v,d] => prontidao[x,d]

	--Quantidade de cada tipo de funcionario
	#Xerife = 1
	#Detetive = 2
	#Novato = 3
	#Veterano = 3

}

--Testa se todo detetive da delegacia está ou na delegacia, ou em alguma ocorrência
assert testeDetetiveSemFuncao {
	all d:Detetive | (one v:Vermelho | (investigando[d,v]) or (one c:Delegacia | prontidao[d,c]))
}

--Testa se há um Xerife trabalhando, enquanto ele podia ter sido substituído por um policial veterano
assert testeXerifePriorizado {
	all x:Xerife | (one o:Ocorrencia | atende[x,o]) => (all v:Veterano | (one c:Ocorrencia | atende[v,c]))
}

check testeDetetiveSemFuncao
check testeXerifePriorizado

pred show[]{
}
run show for 9
