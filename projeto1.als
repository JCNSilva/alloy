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
	clientesVendedor: Cliente lone -> Time
}


sig OperadorDeCaixa extends Funcionario {
	clientesOperador: Cliente lone -> Time
}


sig PromotorDeCartao extends Funcionario {
	clientesPromotor: Cliente lone -> Time
}


sig Cliente {
	nome: one Id, 
	compras: Compra lone -> Time,
	cartoes: Cartao lone -> Time
}


abstract sig Id{}

abstract sig Item {}

sig Calcado, Roupa extends Item {}

abstract sig Compra {
	itens: Item lone -> Time
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
	all com: Compra | all t: Time | one com.~(compras.t)

	//Cada cliente faz no máximo uma compra
	all c: Cliente | all t:Time | lone c.(compras.t)

	//Uma compra deve ter itens
	all com: Compra | all t:Time | some com.(itens.t)
}


fact cartoes {
	//Cada cartão só pode ser relacionado a um cliente
	all car: Cartao | all t:Time | one car.~(cartoes.t)

	//Todo cliente pode ter no máximo um cartão
	all c: Cliente | all t:Time | lone c.(cartoes.t)
}


fact itens {
	//Cada item só pode ser relacionado a uma compra
	all i: Item | all t:Time | one i.~(itens.t)
}


fact cliente {
	//Todo cliente foi atendido por pelo menos um funcionário
	all cliente: Cliente | all t:Time | clienteFoiAtendido[cliente,t]

	//A Id de um cliente deve ser única
	all cliente: Cliente | one cliente.nome

	//Toda Id pertence a um Cliente
	all id: Id | one id.~nome

	//all c: Cliente, prom: Promotor, t: Time, t': Time | 
	//Todo cliente é atendido por um único  ou nenhum promotor
	all c: Cliente | all prom: PromotorDeCartao | all t, t':Time | ehCliente[c, prom,t] and promotorDoClienteNaoMuda[c, prom, t,t']

	//Todo cliente é atendido por um único  ou nenhum operador
	all c: Cliente | all op:OperadorDeCaixa | all t, t':Time | ehCliente[c, op,t] and operadorDoClienteNaoMuda[c, op, t,t']

	//Todo cliente é atendido por um único ou nenhum vendedor
	all c: Cliente | all v: Vendedor | all t, t':Time | ehCliente[c,v,t] and vendedorDoClienteNaoMuda[c, v, t,t']

	//Se um cliente foi atendido por um vendedor, ele também deve ter sido atendido por um operador de caixa
	all c: Cliente | all t:Time | one operadoresAssociados[c,t] implies one vendedoresAssociados[c,t]

	//O cliente só pode ter um cartão se for atendido por um promotor de cartão
	all c: Cliente | all t:Time |  fezCartoes[c,t] implies one promotoresAssociados[c,t]
	
	//O cliente só pode ter um item se for atendido por um vendedor
	all c: Cliente | all t:Time | temItem[c,t] implies one vendedoresAssociados[c,t]

	//O cliente só pode fazer uma compra se for atendido por um operador de caixa
	all c: Cliente | all t:Time | fezCompras[c,t] implies one operadoresAssociados[c,t]
}


/*fact traces {
	init[first]
	all pre: Time - last | let pos = pre.next |
	all c: Cliente, op:OperadorDeCaixa, prom: PromotorDeCartao, v: Vendedor | 
	fazerCartao[c, prom, pre, pos] or
	efetuarVenda[c, v, pre, pos] and
	passarCompra[c, op, pre, pos]
}*/




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

fun vendedoresAssociados[c: Cliente, t: Time]: set Vendedor {
	c.~(clientesVendedor.t)
}

fun promotoresAssociados[c:Cliente, t:Time]: set PromotorDeCartao {
	c.~(clientesPromotor.t)
}

fun operadoresAssociados[c:Cliente, t:Time]: set OperadorDeCaixa {
	c.~(clientesOperador.t)
}

fun itensDeCompra[c: Cliente, t:Time]: set Item{
	(c.(compras.t)).(itens.t)
}


//DECLARAÇÃO DOS PREDICADOS

pred ehCliente[c:Cliente, prom:PromotorDeCartao, t:Time]{
	(c in prom.clientesPromotor.t => (all prom2: PromotorDeCartao - prom | c !in prom2.clientesPromotor.t))
}

pred ehCliente[c:Cliente, op:OperadorDeCaixa, t:Time]{

	(c in op.clientesOperador.t => (all op2: OperadorDeCaixa - op | c !in op2.clientesOperador.t))
}

pred ehCliente[c:Cliente, v:Vendedor, t: Time]{
		(c in v.clientesVendedor.t => (all v2: Vendedor - v | c !in v2.clientesVendedor.t))
}

pred clienteFoiAtendido[cliente:Cliente, t:Time]{
	some cliente.~(clientesVendedor.t) or some cliente.~(clientesOperador.t) or some cliente.~(clientesPromotor.t)
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

pred fezCompras[c:Cliente, t: Time]{
	some c.(compras.t)
}

pred fezCartoes[c:Cliente, t:Time]{
	some c.(cartoes.t)
}

pred temItem[c:Cliente, t:Time]{
	some itensDeCompra[c,t]
}

pred init [t:Time] {
	no clientesPromotor.t
	no clientesVendedor.t
	no clientesOperador.t
}


pred promotorDoClienteNaoMuda[cliente: Cliente, prom: PromotorDeCartao, t,t': Time]{
	prom.(clientesPromotor.t') = prom.(clientesPromotor.t)
}


pred fazerCartao[c:Cliente, prom:PromotorDeCartao, t,t': Time] {
	c !in (prom.clientesPromotor).t
		(prom.clientesPromotor).t' = (prom.clientesPromotor).t + c
	promotorDoClienteNaoMuda[c, prom, t,t']
}

pred vendedorDoClienteNaoMuda[cliente: Cliente, v:Vendedor, t,t': Time]{
	v.(clientesVendedor.t') = v.(clientesVendedor.t)
}

pred efetuarVenda[c:Cliente, v:Vendedor, t,t':Time] {
	c !in (v.clientesVendedor).t
		(v.clientesVendedor).t' = (v.clientesVendedor).t + c
	vendedorDoClienteNaoMuda[c, v, t, t']
}

pred operadorDoClienteNaoMuda[c: Cliente, op: OperadorDeCaixa, t,t': Time]{
	op.(clientesOperador.t') = op.(clientesOperador.t)
}

pred passarCompra[c: Cliente, op: OperadorDeCaixa,t, t': Time]{
	c !in (op.clientesOperador).t
		(op.clientesOperador).t' = (op.clientesOperador).t + c
	operadorDoClienteNaoMuda[c, op, t ,t']
}


 
//DECLARAÇÃO DOS ASSERTS
assert clienteNaoFoiAtendidoPorMuitosVendedores {
	all c:Cliente | all t:Time | #(c.~(clientesVendedor.t)) = 0 or #(c.~(clientesVendedor.t)) = 1
}

assert clienteNaoFoiAtendidoPorMuitosPromotores{
	all c:Cliente | all t:Time | #(c.~(clientesPromotor.t)) = 0 or #(c.~(clientesPromotor.t)) = 1
}

assert clienteNaoFoiAtendidoPorMuitosOperadores {
	all c:Cliente | all t:Time | #(c.~(clientesOperador.t)) = 0 or #(c.~(clientesOperador.t)) = 1
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
	all c: Cliente | all t: Time | no c.~(clientesVendedor.t) implies no c.~(clientesOperador.t)
}




//RUNs E CHECKs
run{} for 11
check aLojaTemVendedores for 11
check aLojaTemPromotores for 11
check aLojaTemOperadores for 11
check clienteNaoFoiAtendidoPorMuitosVendedores for 11
check clienteNaoFoiAtendidoPorMuitosPromotores for 11
check clienteNaoFoiAtendidoPorMuitosOperadores for 11
check seNaoEhClienteVendedorNaoEhClienteOperador for 11



/* TODO LIST */
	//Funções com Time: vender, fazer cartão, passar compra, checar premiacao

//Perguntas
//Pode existir cliente que não faz compras ou cartão? depende
//O cliente pode fazer mais de uma compra? s


