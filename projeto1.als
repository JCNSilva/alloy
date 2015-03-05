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
	//status: Status -> Time
}

sig Vendedor extends Funcionario {
	clientesVendedor: Cliente -> Time
	/*statusVendedorPremiado: statusPremiado one -> Time*/
}


sig OperadorDeCaixa extends Funcionario {
	clientesOperador: Cliente -> Time
	/*statusOperadorPremiado: statusPremiado one -> Time*/
}


sig PromotorDeCartao extends Funcionario {
	clientesPromotor: Cliente -> Time
	/*statusPromotorPremiado: statusPremiado one -> Time*/
}


sig Cliente {
	nome: one Id, 
	compras: Compra -> Time,
	cartoes: Cartao -> Time
}


abstract sig Id{}

abstract sig Item {}

sig Calcado, Roupa extends Item {}

abstract sig Compra {
	itens: Item -> Time
}

sig CompraCheque, CompraAPrazo extends Compra {}

abstract sig Cartao {}

sig CartaoSimples, CartaoComDependente extends Cartao {}

/*
abstract sig StatusPremiado{
}

sig Premiado, NaoPremiado extends StatusPremiado{
}
*/



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
	all v: Vendedor | one v.~vendedores
	all op: OperadorDeCaixa | one op.~operadores
	all prom: PromotorDeCartao | one prom.~promotores
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

	//Todo cliente é atendido por um único  ou nenhum promotor
	all c: Cliente | all prom: PromotorDeCartao | all t, t':Time | ehCliente[c, prom,t,t']

	//Todo cliente é atendido por um único  ou nenhum operador
	all c: Cliente | all op:OperadorDeCaixa | all t, t':Time | ehCliente[c, op,t,t']

	//Todo cliente é atendido por um único ou nenhum vendedor
	all c: Cliente | all v: Vendedor | all t, t':Time | ehCliente[c,v,t,t']

	//Se um cliente foi atendido por um vendedor, ele também deve ter sido atendido por um operador de caixa
	all c: Cliente | all t:Time | one operadoresAssociados[c,t] implies one vendedoresAssociados[c,t]

	//O cliente só pode ter um cartão se for atendido por um promotor de cartão
	all c: Cliente | all t,t':Time |  fezCartoes[c,t] iff one promotoresAssociados[c,t] and cartaoDoClienteNaoMuda[c, t,t']
	
	//O cliente só pode ter um item se for atendido por um vendedor
	all c: Cliente | all t:Time | temItem[c,t] iff one vendedoresAssociados[c,t]

	//O cliente só pode fazer uma compra se for atendido por um operador de caixa
	all c: Cliente | all t,t':Time | fezCompras[c,t] iff one operadoresAssociados[c,t] and comprasDoClienteNaoMudam[c, t, t']
}

/*
fact status {
	all st: Status, t: Time | one st.~(status.t)

	all f: Funcionario, t: Time | one f.status.t
}
*/

//TRACES
pred init[t:Time] {
//#(PromotorDeCartao.clientesPromotor).t = 0
//#(Vendedor.clientesVendedor).t = 0
//#(OperadorDeCaixa.clientesOperador).t = 0


//	 no (PromotorDeCartao.clientesPromotor).t 
 	// no (Vendedor.clientesVendedor).t 
//	no (OperadorDeCaixa.clientesOperador).t
	
}

fact traces {
   init[first]
	all pre: Time-last | let pos = pre.next |
//	one c: Cliente, op:OperadorDeCaixa, prom:PromotorDeCartao,  v: Vendedor | 
	some c: Cliente, prom:PromotorDeCartao |
		fazerCartao[c, prom, pre, pos]// or
	//	some v: Vendedor |
	  // efetuarVenda[c, v, pre, pos] 
	///	passarCompra[c, op, pre, pos]
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

pred ehCliente[c:Cliente, prom:PromotorDeCartao, t,t':Time]{
	(c in prom.clientesPromotor.t => (all prom2: PromotorDeCartao - prom | c !in prom2.clientesPromotor.t))
//	operadorDoClienteNaoMuda[c, op, t,t']
//	vendedorDoClienteNaoMuda[c, v, t, t']
}

pred ehCliente[c:Cliente, op:OperadorDeCaixa, t,t':Time]{
	(c in op.clientesOperador.t => (all op2: OperadorDeCaixa - op | c !in op2.clientesOperador.t))
//	promotorDoClienteNaoMuda[c, prom, t,t']
	// vendedorDoClienteNaoMuda[c, v, t, t']

}

pred ehCliente[c:Cliente, v:Vendedor, t,t': Time]{
	(c in v.clientesVendedor.t => (all v2: Vendedor - v | c !in v2.clientesVendedor.t))
//	promotorDoClienteNaoMuda[c, prom, t,t']
//	operadorDoClienteNaoMuda[c, op, t,t']
}

pred clienteFoiAtendido[c:Cliente, t:Time]{
	some c.~(clientesVendedor.t) or some c.~(clientesOperador.t) or some c.~(clientesPromotor.t)
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


pred vendedorDoClienteNaoMuda[cliente: Cliente, v:Vendedor, t,t': Time]{
	v.(clientesVendedor.t') = v.(clientesVendedor.t)
}


pred promotorDoClienteNaoMuda[cliente: Cliente, prom: PromotorDeCartao, t,t': Time]{
	(prom.clientesPromotor).t' = (prom.clientesPromotor).t
}


pred operadorDoClienteNaoMuda[c: Cliente, op: OperadorDeCaixa, t,t': Time]{
	op.(clientesOperador.t') = op.(clientesOperador.t)
}


pred cartaoDoClienteNaoMuda[c:Cliente, t,t': Time]{
	c.(cartoes.t') = c.(cartoes.t)
}


pred comprasDoClienteNaoMudam[c:Cliente, t,t': Time]{
	c.(compras.t') = c.(compras.t)
	itensDeCompra[c,t'] = itensDeCompra[c,t]
}


//AÇÕES COM TIME



/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pred clienteDoPromotorNaoMudam[promotores: set PromotorDeCartao, t, t' : Time] {-- Os promotores passados como parâmetro não mudam
	all p: promotores | 
		(p.clientesPromotor).t = (p.clientesPromotor).t'
}
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pred clienteDoVendedorNaoMudam[vendedores: set Vendedor, t, t' : Time] {-- Os vendedores passados como parâmetro não mudam
	all p: vendedores | 
		(p.clientesVendedor).t = (p.clientesVendedor).t'
}
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
pred clienteDoOperadorNaoMudam[operadores: set OperadorDeCaixa, t, t' : Time] {-- Os operadores passados como parâmetro não mudam
	all p: operadores | 
		(p.clientesOperador).t = (p.clientesOperador).t'
}
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

pred fazerCartao[c:Cliente, prom:PromotorDeCartao, t,t': Time] {
 // (all prom2: PromotorDeCartao |  c !in (prom2.clientesPromotor).t )
(c not in prom.clientesPromotor.t) => 
	(prom.clientesPromotor).t' = (prom.clientesPromotor).t + c
	
	clienteDoPromotorNaoMudam[PromotorDeCartao - prom, t, t']
 	all v: Vendedor | clienteDoVendedorNaoMudam[v, t, t']
   all o: OperadorDeCaixa | clienteDoOperadorNaoMudam[o, t, t' ]
}


pred efetuarVenda[c:Cliente, v:Vendedor, t,t':Time] {
	  (all v2: Vendedor |  c !in (v2.clientesVendedor).t ) => (v.clientesVendedor).t' = (v.clientesVendedor).t + c

	
 	all p : PromotorDeCartao |	clienteDoPromotorNaoMudam[p, t, t']
   clienteDoVendedorNaoMudam[Vendedor - v, t, t']
   all o: OperadorDeCaixa | clienteDoOperadorNaoMudam[o, t, t' ]
}


pred passarCompra[c: Cliente, op: OperadorDeCaixa,t, t': Time]{
(all o2: OperadorDeCaixa |  c !in (o2.clientesOperador).t ) => (op.clientesOperador).t' = (op.clientesOperador).t + c

	all p : PromotorDeCartao |	clienteDoPromotorNaoMudam[p, t, t']
   all v: Vendedor | clienteDoVendedorNaoMudam[ v, t, t']
   clienteDoOperadorNaoMudam[OperadorDeCaixa - op, t, t' ]
}

/*
pred premiaVendedor[v: Vendedor, t, t': Time]{
	v.(statusVendedor.t) in statusNaoPremiado and 
	(some calcado: Calcado, roupa: Roupa |	(calcado + roupa) in v.(clientesVendedor.t).(compras.t).(itens.t)) implies	v.(statusVendedor.t') = statusPremiado
}

 
pred premiaOperador[op:Operador, t, t': Time]{
	op.(statusOperadorPremiado.t) in statusNaoPremiado and --Um operador de caixa tem que passar
 pelo menos uma compra no cartão em dez vezes e
-- pelo menos uma compra no cartão da loja com cem dias para pagar (Lascou)
	op.(statusOperadorPremiado.t') = statusPremiado
}

pred premiaPromotor[prom: Promotor, t, t': Time]{
	prom.(statusPromotorPremiado.t) in statusNaoPremiado and --deve fazer no mínimo dois cartões de 
--crédito onde pelo menos um com dependente
	prom.(statusPromotorPremiado.t') = statusPremiado
}
*/

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
run{} for 12
check aLojaTemVendedores for 11
check aLojaTemPromotores for 11
check aLojaTemOperadores for 11
check clienteNaoFoiAtendidoPorMuitosVendedores for 11
check clienteNaoFoiAtendidoPorMuitosPromotores for 11
check clienteNaoFoiAtendidoPorMuitosOperadores for 11
check seNaoEhClienteVendedorNaoEhClienteOperador for 11



/* TODO LIST */
	//Funções com Time: checar premiacao


