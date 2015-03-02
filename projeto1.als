module projeto

open util/ordering[Time]



//DECLARAÇÃO DAS ASSINATURAS

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
	compras: set Compra/* -> Time*/,
	cartoes: set Cartao/* -> Time*/
}

sig Id{}

abstract sig Item {}

sig Calcado, Roupa extends Item {}

abstract sig Compra {
	itens: set Item
}

sig CompraCheque, CompraAPrazo extends Compra {}

abstract sig Cartao {}

sig CartaoSimples, CartaoComDependente extends Cartao {}




//DECLARAÇÃO DOS FATOS

fact loja {
	//O numero de vendedores está sempre entre 3 e 5
	all lj: Loja |  #(vendedoresDaLoja[lj]) >= 3 and #(vendedoresDaLoja[lj]) <= 5

	//O número de operadores de caixa é sempre 3 ou 4
	all lj: Loja | #(operadoresDaLoja[lj]) = 3 or #(operadoresDaLoja[lj]) = 4

	//O número de promotores de cartão é sempre 2
	all lj: Loja | #(promotoresDaLoja[lj]) = 2
}


fact funcionarios {
	//Todo funcionário está empregado em uma loja
	all v: Vendedor | some v.~vendedores
	all op: OperadorDeCaixa | some op.~operadores
	all prom: PromotorDeCartao | some prom.~promotores
}


fact compras {
	//Cada compra só pode ser relacionado a um cliente
	all com: Compra | one com.~compras

	//Cada cliente faz no máximo uma compra
	all c: Cliente | lone c.compras

	//Uma compra deve ter itens
	all com: Compra | some com.itens
}


fact cartoes {
	//Cada cartão só pode ser relacionado a um cliente
	all car: Cartao | one car.~cartoes

	//Todo cliente pode ter no máximo um cartão
	all c: Cliente | lone c.cartoes
}


fact itens {
	//Cada item só pode ser relacionado a um cliente
	all i: Item | one i.~itens
}


fact cliente {
	//Todo cliente foi atendido por pelo menos um funcionário
	all cliente: Cliente | some cliente.~clientes

	//A Id de um cliente deve ser única
	all cliente: Cliente | one cliente.nome

	//Toda Id pertence a um Cliente
	all id: Id | one id.~nome

	//O cliente só pode ter um cartão se for atendido por um promotor de cartão
	all prom: PromotorDeCartao | all c: Cliente |  fezCartoes[c] implies ehCliente[c, prom]

	//O cliente só pode fazer uma compra se for atendido por um operador de caixa
	all op: OperadorDeCaixa | all c: Cliente | fezCompras[c] implies ehCliente[c, op]

	//O cliente só pode ter um item se for atendido por um vendedor
	all v: Vendedor | all c: Cliente | temItem[c] implies ehCliente[c,v]

	//Se um cliente foi atendido por um vendedor, ele também deve ter sido atendido por um operador de caixa
	all op: OperadorDeCaixa | all v: Vendedor | all c: Cliente | ehCliente[c, op] implies ehCliente[c, v]
}



//DECLARAÇÃO DAS FUNÇÕES

fun vendedoresDaLoja[lj: Loja]: set Vendedor {
	lj.vendedores
}

fun promotoresDaLoja[lj: Loja]: set PromotorDeCartao{
	lj.promotores
}

fun operadoresDaLoja[lj: Loja]: set OperadorDeCaixa{
	lj.operadores
}


//DECLARAÇÃO DOS PREDICADOS

pred show[]{}

pred ehCliente[c:Cliente, f:Funcionario]{
	c in f.clientes
}

pred ehVendedor[f: Funcionario, lj: Loja] {
	f in lj.vendedores
}

pred ehOperadorDeCaixa[f: Funcionario, lj: Loja]{
	f in lj.operadores
}

pred ehPromotorDeCaixa[f: Funcionario, lj: Loja]{
	f in lj.promotores
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



//DECLARAÇÃO DOS ASSERTS


//RUNs E CHECKs
run show for 11

/* TODO LIST */
	//Funções com Time: vender, fazer cartão, passar compra, checar premiacao

//Perguntas
//Pode existir cliente que não faz compras ou cartão?
//O cliente pode ter mais de um cartão?
//O cliente pode fazer mais de uma compra?
//O cliente pode ser atendido por mais de um funcionario do mesmo tipo?


