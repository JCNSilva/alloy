module projeto

open util/ordering[Time]


//DECLARAÇÃO DAS ASSINATURAS

sig Time {}

one sig Loja {
	vendedores: some Vendedor,
	operadores: some OperadorDeCaixa,
	promotores: some PromotorDeCartao
}

abstract sig Funcionario {}

sig Vendedor extends Funcionario {
	clientesVendedor: set Cliente
}

sig OperadorDeCaixa extends Funcionario {
	clientesOperador: set Cliente
}

sig PromotorDeCartao extends Funcionario {
	clientesPromotor: set Cliente
}

sig Cliente {
	nome: one Id, 
	compras: set Compra/* -> Time*/,
	cartoes: set Cartao/* -> Time*/
	/* Msm raciocinio
	compras: Compra lone -> Time,
	cartoes: Cartao lone -> Time
	*/
}

sig Id{}

abstract sig Item {}

sig Calcado, Roupa extends Item {}

abstract sig Compra {
	itens: set Item
	/* Não deveria ser Time tmb?*/
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
	//Cada item só pode ser relacionado a uma compra
	all i: Item | one i.~itens
}


fact cliente {
	//Todo cliente foi atendido por pelo menos um funcionário
	all cliente: Cliente | clienteFoiAtendido[cliente]

	//A Id de um cliente deve ser única
	all cliente: Cliente | one cliente.nome

	//Toda Id pertence a um Cliente
	all id: Id | one id.~nome

	//Todo cliente é atendido por um ou nenhum promotor
	all c: Cliente | lone prom: PromotorDeCartao | ehCliente[c, prom]

	//Todo cliente é atendido por um ou nenhum operador
	all c: Cliente | lone op:OperadorDeCaixa | ehCliente[c, op]

	//Todo cliente é atendido por um ou nenhum vendedor
	all c: Cliente | lone v: Vendedor | ehCliente[c,v]

	//Se um cliente foi atendido por um vendedor, ele também deve ter sido atendido por um operador de caixa
	all c: Cliente | one operadoresAssociados[c] implies one vendedoresAssociados[c]

	//O cliente só pode ter um cartão se for atendido por um promotor de cartão
	all c: Cliente | fezCartoes[c] implies one promotoresAssociados[c]
	
	//O cliente só pode ter um item se for atendido por um vendedor
	all c: Cliente | temItem[c] implies one vendedoresAssociados[c]

	//O cliente só pode fazer uma compra se for atendido por um operador de caixa
	all c: Cliente | fezCompras[c] implies one operadoresAssociados[c]
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

fun vendedoresAssociados[c:Cliente]: set Vendedor {
	c.~clientesVendedor
}

fun promotoresAssociados[c:Cliente]: set PromotorDeCartao {
	c.~clientesPromotor
}

fun operadoresAssociados[c:Cliente]: set OperadorDeCaixa {
	c.~clientesOperador
}


//DECLARAÇÃO DOS PREDICADOS

pred show[]{}

pred ehCliente[c:Cliente, prom:PromotorDeCartao]{
	c in prom.clientesPromotor
}

pred ehCliente[c:Cliente, op:OperadorDeCaixa]{
	c in op.clientesOperador 
}

pred ehCliente[c:Cliente, v:Vendedor]{
	c in v.clientesVendedor
}

pred clienteFoiAtendido[cliente:Cliente]{
	some cliente.~clientesVendedor or some cliente.~clientesOperador or some cliente.~clientesPromotor
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
assert clienteNaoFoiAtendidoPorMuitosVendedores {
	all c:Cliente | #(c.~clientesVendedor) = 0 or #(c.~clientesVendedor) = 1
}

assert clienteNaoFoiAtendidoPorMuitosPromotores{
	all c:Cliente | #(c.~clientesPromotor) = 0 or #(c.~clientesPromotor) = 1
}

assert clienteNaoFoiAtendidoPorMuitosOperadores {
	all c:Cliente | #(c.~clientesOperador) = 0 or #(c.~clientesOperador) = 1
}

assert aLojaTemVendedores{
	all l:Loja | #vendedoresDaLoja[l] > 0
}

assert aLojaTemPromotores{
	all l:Loja | #promotoresDaLoja[l] > 0
}

assert aLojaTemOperadores{
	all l:Loja | #operadoresDaLoja[l] > 0
}

assert seNaoEhClienteVendedorNaoEhClienteOperador{
	all c: Cliente | no c.~clientesVendedor implies no c.~clientesOperador
}


//RUNs E CHECKs
run show for 11
--check aLojaTemVendedores for 11
--check aLojaTemPromotores for 11
--check aLojaTemOperadores for 11
--check clienteNaoFoiAtendidoPorMuitosVendedores for 11
--check clienteNaoFoiAtendidoPorMuitosPromotores for 11
--check clienteNaoFoiAtendidoPorMuitosOperadores for 11
--check seNaoEhClienteVendedorNaoEhClienteOperador for 11



/* TODO LIST */
	//Funções com Time: vender, fazer cartão, passar compra, checar premiacao

//Perguntas
//Pode existir cliente que não faz compras ou cartão? depende
//O cliente pode ter mais de um cartão? n
//O cliente pode fazer mais de uma compra? s
//O cliente pode ser atendido por mais de um funcionario do mesmo tipo? n


