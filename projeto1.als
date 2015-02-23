module projeto

open util/ordering[Time]

one sig Loja {
	vendedores: some Vendedor,
	operadores: some OperadorDeCaixa,
	promotores: some PromotorDeCartao
}

abstract sig Funcionario {
	
}

sig Vendedor extends Funcionario {
	
}

sig OperadorDeCaixa extends Funcionario {
	
}

sig PromotorDeCartao extends Funcionario {

}

sig Time {

}

fact {
	//O numero de vendedores está sempre entre 3 e 5
	all lj: Loja |  #(lj.vendedores) >= 3 and #(lj.vendedores) <= 5

	//O número de operadores de cixa é sempre 3 ou 4
	all lj: Loja | #(lj.operadores) = 3 or #(lj.operadores) = 4

	//O número de promotores de cartão é sempre 2
	all lj: Loja | #(lj.promotores) = 2

	//Todo funcionário está empregado em uma loja
	all v: Vendedor | one v.~vendedores
	all op: OperadorDeCaixa | one op.~operadores
	all prom: PromotorDeCartao | one prom.~promotores
}

pred show[]{}
run show for 11

//Métodos com Time: vender, fazer cartão, passar compra, checar premiacao
//Assinaturas Brinde, Pessoa, Id, Item(Calçado, Roupa), Compra(A vista, prazo), Cartão
