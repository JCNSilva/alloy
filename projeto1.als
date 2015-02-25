module projeto

open util/ordering[Time]

sig Time {}

one sig Loja {
	vendedores: some Vendedor,
	operadores: some OperadorDeCaixa,
	promotores: some PromotorDeCartao
}

abstract sig Funcionario {
	clientes: set Cliente
}

sig Vendedor, OperadorDeCaixa, PromotorDeCartao extends Funcionario {}

sig Cliente {
	nome: one Id,
	itens: set Item,
	compras: set Compra,
	cartoes: set Cartao
}

sig Id {}

abstract sig Item {}

sig Calcado, Roupa extends Item {}

abstract sig Compra {}

sig CompraCheque, CompraAPrazo extends Compra {}

abstract sig Cartao {}

sig CartaoSimples, CartaoComDependente extends Cartao {}

//mudanca
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
	all prom: PromotorDeCartao | all c: Cliente | c not in prom.clientes implies  #(c.cartoes) = 0
	
	//Cada cartão só pode ser relacionado a um cliente
	all car: Cartao | one car.~cartoes

	//O cliente só pode fazer uma compra se for atendido por um operador de caixa
	all op: OperadorDeCaixa | all c: Cliente | c not in op.clientes implies  #(c.compras) = 0

	//Cada compra só pode ser relacionado a um cliente
	all com: Compra | one com.~compras

	//O cliente só pode ter um item se for atendido por um vendedor
	all v: Vendedor | all c: Cliente | c not in v.clientes implies  #(c.itens) = 0

	//Cada item só pode ser relacionado a um cliente
	all i: Item | one i.~itens

}

pred show[]{}
run show for 11

/* TODO LIST */
	//O cliente só pode ter um cartão se for atendido por um promotor de cartão
	//O cliente só pode fazer uma compra se for atendido por um operador de caixa
	//O cliente só pode ter um item se for atendido por um vendedor
	//Funções com Time: vender, fazer cartão, passar compra, checar premiacao


