module projeto

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

fact {
	all lj: Loja |  #(lj.vendedores) = 3 or #(lj.vendedores) = 4 or #(lj.vendedores) = 5
	all lj: Loja | #(lj.operadores) = 3 or #(lj.operadores) = 4
	all lj: Loja | #(lj.promotores) = 2
//para todo funcionario, existe uma unica loja, tal que funcionario trabalha na loja (funcionario -> loja)
}

pred ehFuncionario[lj : Loja]{
	some lj.vendedores
}

pred show[]{}
run show for 11


//so pode existir funcionario se existir uma loja
