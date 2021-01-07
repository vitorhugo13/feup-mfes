abstract sig TYPE {}
one sig click, text, select extends TYPE {}

sig PARAMS {}
sig URL {}

sig Acao {
	tipo : one TYPE,
	params : set PARAMS,
	url : lone URL
}

sig TracoEx {
	init : one URL,
	traco : Int one -> Acao
}

--1.1
fun acoesComAlteracaoDePagina[tr: TracoEx]: set Acao{
	{ a: (Int.(tr.traco)) | one a.url }
}

--1.2
fun primeiraAcao[tr: TracoEx]: Acao {
	{ a: (Int.(tr.traco)) | one a.url and a.url = tr.init }
}

--1.3
fact mesmoURL{
	all tr: TracoEx | tr.init = (tr.primeiraAcao).url
}

--1.4
fun URLultimaAcao[tr: TracoEx]: URL {
	(ultimaAcao[tr]).url
}

fun ultimaAcao[tr: TracoEx]: Acao{
	{ 
	a: Acao | all a2: acoesComAlteracaoDePagina[tr] | 
		a in acoesComAlteracaoDePagina[tr] and a != a2 and (tr.traco).a > (tr.traco).a2 

	}
}

--1.5
fact URLdiferentes{
	all disj a1, a2: acoesComAlteracaoDePagina[TracoEx] | TracoEx.traco.a1 = TracoEx.traco.a2.minus[1] => a1.url != a2.url
}

run {}