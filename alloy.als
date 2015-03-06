module projeto

open util/ordering[Time]


------------------------------------------------------------DECLARAÇÃO DAS ASSINATURAS--------------------------------------------------

sig Time {}

one sig Loja {
	vendedores: set Vendedor,
	operadores: set OperadorDeCaixa,
	promotores: set PromotorDeCartao,
	clientes: Cliente -> Time
}

abstract sig Funcionario {}

sig Vendedor extends Funcionario {
	clientesVendedor: Cliente -> Time
}

sig OperadorDeCaixa extends Funcionario {
	clientesOperador: Cliente -> Time
}

sig PromotorDeCartao extends Funcionario {
	clientesPromotor: Cliente -> Time
}

sig Cliente {
	nome: one Id, 
	compras: Compra -> Time,
	cartoes: Cartao one -> Time
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

-----------------------------------------------------FATOS-------------------------------------------------------------------------------------------------------------------------

fact traces{
	init[first]
	all pre: Time-last | let pos = pre.next |
	some c: Cliente, prom:PromotorDeCartao, op: OperadorDeCaixa, v:Vendedor |
		fazerCartao[c, prom, pre, pos]  or 
       efetuarVenda[c, v, pre, pos] or
	    passarCompra[c, op,pre,pos]
}

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


fact cliente {
	//Todo cliente foi atendido por pelo menos um funcionário
	all cli: Cliente , t: Time| one cli.~(clientes.t)

	//A Id de um cliente deve ser única
	all cliente: Cliente | one cliente.nome

	//Toda Id pertence a um Cliente
	all id: Id | one id.~nome

	//Todo cliente é atendido por um único  ou nenhum promotor
	all c: Cliente, prom: PromotorDeCartao, t:Time |  ehClienteDeUmPromotor[c, prom,t]

	//Todo cliente é atendido por um único  ou nenhum operador
	all c: Cliente, op:OperadorDeCaixa, t:Time | ehClienteDeUmOperador[c, op,t]

	//Todo cliente é atendido por um único ou nenhum vendedor
	all c: Cliente, v: Vendedor, t:Time | ehClienteDeUmVendedor[c,v,t]

	//Quem tem um cartão, foi atendido por um promotor de cartão
	all c: Cliente, t:Time | some c.cartoes.t => some c.~(clientesPromotor.t)
}

fact cartoes {
	//Todo cartão só possui um dono
	all card: Cartao, t:Time | one card.~(cartoes.t)
}

fact comprasEItens {
	all compra: Compra, t: Time | one compra.~(compras.t)
	all item: Item, t: Time | one item.~(itens.t)
	all c: Cliente, t: Time | lone c.compras.t
	all compra: Compra, t: Time | some compra.itens.t
}

-------------------------------------------------------FUNÇÕES---------------------------------------------------------------------------------------------------------------

fun vendedoresDaLoja[lj: Loja]: set Vendedor {
	lj.vendedores
}

fun promotoresDaLoja[lj: Loja]: set PromotorDeCartao{
	lj.promotores
}

fun operadoresDaLoja[lj: Loja]: set OperadorDeCaixa{
	lj.operadores
}



------------------------------------------------PREDICADOS----------------------------------------------------------------------------------------------------
pred init[t:Time] {
	/*#(PromotorDeCartao.clientesPromotor).t = 0
	#(Vendedor.clientesVendedor).t = 0
	#(OperadorDeCaixa.clientesOperador).t = 0
//	#(Cliente.cartoes).t = 0*/
}


pred clienteFoiAtendido[c:Cliente, t:Time]{
	some	 c.~(clientesVendedor.t) or  some c.~(clientesOperador.t) or some c.~(clientesPromotor.t)
}

pred ehClienteDeUmPromotor[c:Cliente, prom:PromotorDeCartao, t:Time]{
	(c in prom.clientesPromotor.t => (all prom2: PromotorDeCartao - prom | c !in prom2.clientesPromotor.t))

}

pred ehClienteDeUmOperador[c:Cliente, op:OperadorDeCaixa, t:Time]{
	(c in op.clientesOperador.t => (all op2: OperadorDeCaixa - op | c !in op2.clientesOperador.t))

}


pred ehClienteDeUmVendedor[c:Cliente, v:Vendedor, t: Time]{
	(c in v.clientesVendedor.t => (all v2: Vendedor - v | c !in v2.clientesVendedor.t))
}


-- Os promotores passados como parâmetro não mudam
pred clienteDoPromotorNaoMudam[promotores: set PromotorDeCartao, t, t' : Time] {
	all p: promotores | 
		(p.clientesPromotor).t' = (p.clientesPromotor).t
}

-- Os vendedores passados como parâmetro não mudam
pred clienteDoVendedorNaoMudam[vendedores: set Vendedor, t, t' : Time] {
	all p: vendedores | 
		(p.clientesVendedor).t' = (p.clientesVendedor).t

}

-- Os operadores passados como parâmetro não mudam
pred clienteDoOperadorNaoMudam[operadores: set OperadorDeCaixa, t, t' : Time] {
	all p: operadores | 
		(p.clientesOperador).t' = (p.clientesOperador).t
}


-----------------------------------------------------------------OPERAÇÕES---------------------------------------------------------------------------------------------------------

pred fazerCartao[c:Cliente, prom:PromotorDeCartao, t,t': Time] {

   all prom2: PromotorDeCartao  | c !in (prom2.clientesPromotor).t =>  (prom.clientesPromotor).t' = (prom.clientesPromotor).t + c
   all prom2 :PromotorDeCartao |	clienteDoPromotorNaoMudam[prom2 - prom, t, t']
   all v: Vendedor | clienteDoVendedorNaoMudam[v, t, t']
   all o: OperadorDeCaixa | clienteDoOperadorNaoMudam[o, t, t' ]
	all c2: Cliente | one card: Cartao | card !in (c2.cartoes).t => c.cartoes.t' = c.cartoes.t + card
}


pred efetuarVenda[c:Cliente, v:Vendedor, t,t':Time] {
	all v2: Vendedor | c !in (v2.clientesVendedor).t => (v.clientesVendedor).t' = (v.clientesVendedor).t + c
   all p : PromotorDeCartao |	clienteDoPromotorNaoMudam[p, t, t']
   all v2: Vendedor | clienteDoVendedorNaoMudam[v2 - v, t, t']
   all o: OperadorDeCaixa | clienteDoOperadorNaoMudam[o, t, t' ]
}


pred passarCompra[c: Cliente, op: OperadorDeCaixa,t, t': Time]{
	all op2: OperadorDeCaixa | c !in (op2.clientesOperador).t => (op.clientesOperador).t' = (op.clientesOperador).t + c
	one c.~(clientesVendedor.t)
	all p : PromotorDeCartao |	clienteDoPromotorNaoMudam[p, t, t']
   all v: Vendedor | clienteDoVendedorNaoMudam[ v, t, t']
	all op2: OperadorDeCaixa | clienteDoOperadorNaoMudam[op2 - op, t, t' ]
	all c2: Cliente | one compra: Compra | compra !in (c2.compras).t => c.compras.t' = c.compras.t + compra
}


---------------------------------------------------------------ASSERTS---------------------------------------------------------------------------------------
assert soPassaCompraSeEfetuarVenda{
	all c: Cliente, op: OperadorDeCaixa, t: Time - last | let t' = t.next | passarCompra[c, op, t, t'] => one c.~(clientesVendedor.t)
}

assert todaCompraTemItens {
	all com: Compra, t: Time | some com.itens.t
}

assert todoItemPertenceAUmaUnicaCompra {
	all item: Item, t: Time | one item.~(itens.t)
}


run{} for 11
check soPassaCompraSeEfetuarVenda for 10
check todaCompraTemItens for 10
check todoItemPertenceAUmaUnicaCompra for 10
