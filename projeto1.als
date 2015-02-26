module projeto

open util/ordering[Time]

//ASSINATURAS

sig Time {}

one sig Loja {
	vendedores: some Vendedor,
	operadores: some OperadorDeCaixa,
	promotores: some PromotorDeCartao
}

abstract sig Funcionario {
	clientes: set Cliente// -> Time
}

sig Vendedor, OperadorDeCaixa, PromotorDeCartao extends Funcionario {}

sig Cliente {
	nome: one Id,
	/*itens: set Item -> Time*/,
	compras: set Compra/* -> Time*/,
	cartoes: set Cartao/* -> Time*/
}

sig Id {}

abstract sig Item {}

sig Calcado, Roupa extends Item {}

abstract sig Compra {
	itens: set Item
}

sig CompraCheque, CompraAPrazo extends Compra {}

abstract sig Cartao {}

sig CartaoSimples, CartaoComDependente extends Cartao {}



//DECLARAÇÃO DOS FATOS

fact {
	//O numero de vendedores está sempre entre 3 e 5
	all lj: Loja |  #(lj.vendedores) >= 3 and #(lj.vendedores) <= 5

	//O número de operadores de caixa é sempre 3 ou 4
	all lj: Loja | #(lj.operadores) = 3 or #(lj.operadores) = 4

	//O número de promotores de cartão é sempre 2
	all lj: Loja | #(lj.promotores) = 2

	//Todo funcionário está empregado em uma loja
	all v: Vendedor | one v.~vendedores
	all op: OperadorDeCaixa | one op.~operadores
	all prom: PromotorDeCartao | one prom.~promotores

	//Todo cliente foi atendido por pelo menos um funcionário
	all cliente: Cliente | some cliente.~clientes

	//A Id de um cliente deve ser única
	all cliente: Cliente | one cliente.nome

	//Toda Id pertence a um Cliente
	all id: Id | one id.~nome

	//O cliente só pode ter um cartão se for atendido por um promotor de cartão
	all prom: PromotorDeCartao | all c: Cliente |  fezCartoes[c] implies ehCliente[c, prom]
	
	//Cada cartão só pode ser relacionado a um cliente
	all car: Cartao | one car.~cartoes

	//Todo cliente pode ter no máximo um cartão
	all c: Cliente | lone c.cartoes

	//O cliente só pode fazer uma compra se for atendido por um operador de caixa
	all op: OperadorDeCaixa | all c: Cliente | fezCompras[c] implies ehCliente[c, op]

	//Cada compra só pode ser relacionado a um cliente
	all com: Compra | one com.~compras

	//Cada cliente faz no máximo uma compra
	all c: Cliente | lone c.compras

	//Uma compra deve ter itens
	all com: Compra | some com.itens

	//O cliente só pode ter um item se for atendido por um vendedor
	all v: Vendedor | all c: Cliente | temItem[c] implies ehCliente[c,v]

	//Cada item só pode ser relacionado a um cliente
	all i: Item | one i.~itens

	//Se um cliente foi atendido por operador de caixa, ele também deve ter sido atendido por um vendedor
	all op: OperadorDeCaixa | all v: Vendedor | all c: Cliente | c in v.clientes iff c in op.clientes

}



//DECLARAÇÃO DOS PREDICADOS

pred show[]{}

pred ehCliente[c:Cliente, f:Funcionario]{
	c in f.clientes
}

pred fezCompras[c:Cliente]{
	some c.compras
}

pred fezCartoes[c:Cliente]{
	some c.cartoes
}

pred temItem[c:Cliente]{
	some (c.compras).itens
}

/*pred venda[v:Vendedor, c:Cliente, i:Item, t,t':Time] {
	
	c not in (v.clientes).t
	(v.clientes).t' = (v.clientes).t + c
	(c.itens).t' = (c.itens).t + i
	
}*/


run show for 11

/* TODO LIST */
	//Funções com Time: vender, fazer cartão, passar compra, checar premiacao
	//Numero de compras <= numero de itens (???)



