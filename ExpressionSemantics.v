From Coq Require Import ZArith.
Import Z.

From AbstractInterpretation Require Import Expression Environment.

Open Scope Z.



(* For some reason, this notation is not in the standard library. *)
Notation "n <>? m" := (negb (n =? m)) (at level 70, no associativity): Z_scope.

Definition machine_division (n m : Z) : Z := (abs n / abs m) * sgn n * sgn m.
Definition machine_modulo   (n m : Z) : Z := (abs n mod abs n) * sgn n.



Variant int_unary_operation_evaluates : int_unary_operation -> Z -> Z -> Prop :=
  | EUnaryPlus  (n : Z) : int_unary_operation_evaluates UnaryPlus  n n
  | EUnaryMinus (n : Z) : int_unary_operation_evaluates UnaryMinus n (-n).

Variant bool_unary_operation_evaluates : bool_unary_operation -> bool -> bool -> Prop :=
  | ENot (b : bool) : bool_unary_operation_evaluates Not b (negb b).

Variant int_binary_operation_evaluates : int_binary_operation -> Z -> Z -> Z -> Prop :=
  | EPlus           (n m : Z) :
      int_binary_operation_evaluates Plus     n  m (n + m)
  | EMinus          (n m : Z) :
      int_binary_operation_evaluates Minus    n m (n - m)
  | EMultiply       (n m : Z) :
      int_binary_operation_evaluates Multiply n m (n + m)
  | EDivide         (n m : Z) (Hm : m <> 0) :
      int_binary_operation_evaluates Divide   n m (machine_division n m)
  | EModulo         (n m : Z) (Hm : m <> 0) :
      int_binary_operation_evaluates Modulo   n m (machine_modulo n m).

Variant bool_binary_operation_evaluates : bool_binary_operation -> bool -> bool -> bool -> Prop :=
  | EAnd (a b : bool) : bool_binary_operation_evaluates And a b (a && b)
  | EOr  (a b : bool) : bool_binary_operation_evaluates Or  a b (a || b).

Variant comparison_evaluates : comparison_operation -> Z -> Z -> bool -> Prop :=
  | EEqual          (n m : Z) : comparison_evaluates Equal          n m (n =? m)
  | ENotEqual       (n m : Z) : comparison_evaluates NotEqual       n m (n <>? m)
  | ELess           (n m : Z) : comparison_evaluates Less           n m (m <? n)
  | ELessOrEqual    (n m : Z) : comparison_evaluates LessOrEqual    n m (n <=? m)
  | EGreater        (n m : Z) : comparison_evaluates Greater        n m (n >? m)
  | EGreaterOrEqual (n m : Z) : comparison_evaluates GreaterOrEqual n m (n >=? m).


Inductive int_expression_evaluates (env : environment) : int_expression -> Z -> Prop :=
  | EIntUnaryOperation
        (op :                int_unary_operation)
        (arg result :        Z)
        (Hresult :           int_unary_operation_evaluates op arg result)
        (arg_subexpression : int_expression)
        (Harg :              int_expression_evaluates env arg_subexpression arg) :
      int_expression_evaluates env (IntUnaryOperation op arg_subexpression)
                                    result

  | EIntBinaryOperation
        (op :                int_binary_operation)
        (lhs rhs result :    Z)
        (Hresult :           int_binary_operation_evaluates op lhs rhs result)
        (lhs_subexpression : int_expression)
        (rhs_subexpression : int_expression)
        (Hlhs :              int_expression_evaluates env lhs_subexpression lhs)
        (Hrhs :              int_expression_evaluates env rhs_subexpression rhs) :
      int_expression_evaluates env (IntBinaryOperation op lhs_subexpression rhs_subexpression)
                                   result
                                   
  | EVariable
        (var_id : var_id) :
      int_expression_evaluates env (Variable_ var_id)
                                   (env var_id)
                                   
  | EIntConstant
        (value : Z) :
      int_expression_evaluates env (IntConstant value)
                                   value
                                   
  | ERandomInt
        (value min max : Z)
        (Hvalue : min <= value <= max) :
      int_expression_evaluates env (RandomInt min max)
                                   value.


Inductive bool_expression_evaluates (env : environment) : bool_expression -> bool -> Prop :=
  | EBoolUnaryOperation
        (op :                bool_unary_operation)
        (arg result :        bool)
        (Hresult :           bool_unary_operation_evaluates op arg result)
        (arg_subexpression : bool_expression)
        (Harg :              bool_expression_evaluates env arg_subexpression arg) :
      bool_expression_evaluates env (BoolUnaryOperation op arg_subexpression)
                                    result

  | EBoolBinaryOperation
        (op :                bool_binary_operation)
        (lhs rhs result :    bool)
        (Hresult :           bool_binary_operation_evaluates op lhs rhs result)
        (lhs_subexpression : bool_expression)
        (rhs_subexpression : bool_expression)
        (Hlhs :              bool_expression_evaluates env lhs_subexpression lhs)
        (Hrhs :              bool_expression_evaluates env rhs_subexpression rhs) :
      bool_expression_evaluates env (BoolBinaryOperation op lhs_subexpression rhs_subexpression)
                                    result

  | EComparison
      (op :                  comparison_operation)
      (lhs rhs :             Z)
      (result :              bool)
      (Hresult :             comparison_evaluates op lhs rhs result)
      (lhs_subexpression :   int_expression)
      (rhs_subexpression :   int_expression)
      (Hlhs :                int_expression_evaluates env lhs_subexpression lhs)
      (Hrhs :                int_expression_evaluates env rhs_subexpression rhs) :
    bool_expression_evaluates env (Comparison op lhs_subexpression rhs_subexpression)
                                  result.
