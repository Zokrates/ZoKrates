# Grammar

The current syntax of ZoKrates is the following
```k
module ZOKRATES-SYNTAX
	imports DOMAINS-SYNTAX

	syntax Prog ::= Impts FunDecls [klabel(#Prog)] // should not be required, cf https://github.com/kframework/k-legacy/issues/1839

	syntax ImptBody ::= "import" String
	syntax Alias ::= "as" Id
	syntax Impt ::= ImptBody [klabel(#Impt)]
	        	  | ImptBody Alias [klabel(#AliasedImpt)]
	syntax Impts ::= List{Impt,""}

  	syntax Id ::= "main" [token]

	syntax Arg ::= Type Id
				 | "private" Type Id

	syntax Type ::= "field"
				  | "bool"
	syntax ReturnTypes ::= List{Type,","}

	syntax Args ::= List{Arg,","}
	syntax FunDecl ::= "def" Id "(" Args ")" "->" "(" ReturnTypes ")" ":" Stmts
	syntax FunDecls ::= FunDecl
                 	  | FunDecl FunDecls                          [right]

	syntax Stmt ::= Assert
				  | Define
				  | Declare
				  | DeclareDefine
				  | Return
				  | For
				  | Destructure

	syntax HintId ::= Id
	                | Type Id

	syntax HintIds ::= List{HintId,","}

	syntax Destructure ::= HintId "," HintIds "=" FCall

	syntax Stmts ::= List{Stmt,""}

	syntax Assert ::= Exp "==" Exp
	syntax Declare ::= Type Id
	syntax Define ::= Id "=" Exp
	syntax DeclareDefine ::= Type Id "=" Exp // should be sugar for Declare then Define
	syntax Return ::= "return" Exps
	syntax For ::= "for" Type Id "in" Int ".." Int "do" Stmts "endfor"


	syntax Exps ::= List{Exp,","}          [strict]
	syntax Exp ::= Int | Bool | Id
               | "(" Exp ")"             [bracket]
               > Exp "(" Exps ")"        [strict]
               > left:
                 Exp "*" Exp             [strict, left]
               | Exp "/" Exp             [strict, left]
               | Exp "**" Exp 		     [strict, left]
               > left:
                 Exp "+" Exp             [strict, left]
               | Exp "-" Exp             [strict, left]
               | IfElse
               > non-assoc:
                 Exp "<" Exp             [strict, non-assoc]
               | Exp "<=" Exp            [strict, non-assoc]
               | Exp ">" Exp             [strict, non-assoc]
               | Exp ">=" Exp            [strict, non-assoc]
               | Exp "==" Exp            [strict, non-assoc]
               > IfElse
               > FCall

    syntax FCall ::= Id "(" Exps ")"

    syntax IfElse ::= "if" Exp "then" Exp "else" Exp "fi"    [strict(1)]

endmodule
```
