sig Name {}
sig Pessoa {
    n: one Name,
    descendentes : set Pessoa
}

fun getAsc[p: Pessoa]: set Pessoa{
    {descendentes.p}
}
-- 11.a) pessoa só tenha dois ascendentes
fact restricaoAscendentes{
    all p: Pessoa | #getAsc[p] = 2
}

-- 11.b) Escreva uma operação que retorne, caso exista, a Pessoa origem, ou seja, a Pessoa
--       de quem todas as outras pessoas descendem. Se não existir uma Pessoa nessas condições deverá
--       retornar o conjunto vazio.

fun originPerson : Pessoa{
    {p: Pessoa | all p': Pessoa - p | p' in p.^descendentes}
}
run {} for 6