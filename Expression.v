From Coq Require Import ZArith.

From AbstractInterpretation Require Import Environment.


Variant int_unary_operation :   Set := UnaryPlus | UnaryMinus.
Variant bool_unary_operation :  Set := Not.
Variant int_binary_operation :  Set := Plus | Minus | Multiply | Divide | Modulo.
Variant bool_binary_operation : Set := And | Or.
Variant comparison_operation :  Set := Equal | NotEqual | Less | LessOrEqual | Greater
                                        | GreaterOrEqual.

Inductive int_expression : Set :=
  | IntUnaryOperation :  int_unary_operation -> int_expression -> int_expression
  | IntBinaryOperation : int_binary_operation -> int_expression -> int_expression -> int_expression
  | Variable_ :          var_id -> int_expression
  | IntConstant :        Z -> int_expression
  | RandomInt (min max : Z) : int_expression.

Inductive bool_expression : Set :=
  | BoolUnaryOperation :  bool_unary_operation -> bool_expression -> bool_expression
  | BoolBinaryOperation : bool_binary_operation -> bool_expression -> bool_expression ->
                                                                        bool_expression
  | Comparison :          comparison_operation -> int_expression -> int_expression ->
                                                                        bool_expression.
  