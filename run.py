from typing import List, Union
import re


class Formula:
    def __init__(self, type: str, content: Union[List['Formula'], List[str], 'Formula', str]):
        self.type = type
        self.content = content

    def __repr__(self):
        return f"{self.type}({self.content})"

    def replace_variable(self, old_var: str, new_var: str) -> 'Formula':
        if self.type == 'PRED':
            self.content = [new_var if item == old_var else item for item in self.content]
        elif self.type in ['AND', 'OR']:
            for i, subf in enumerate(self.content):
                self.content[i] = subf.replace_variable(old_var, new_var)
        elif self.type == 'NOT':
            self.content[0] = self.content[0].replace_variable(old_var, new_var)
        return self


def formula_to_string(formula: Formula) -> str:
    if formula.type == 'PRED':
        return f"{formula.content[0]}({','.join(formula.content[1:])})"
    elif formula.type == 'NOT':
        return f"¬{formula_to_string(formula.content[0])}"
    elif formula.type in ['AND', 'OR']:
        op = ' ∧ ' if formula.type == 'AND' else ' ∨ '
        return f"({op.join(formula_to_string(subf) for subf in formula.content)})"
    elif formula.type == 'IMPL':
        return f"({formula_to_string(formula.content[0])} → {formula_to_string(formula.content[1])})"
    elif formula.type == 'EQUIV':
        return f"({formula_to_string(formula.content[0])} ↔ {formula_to_string(formula.content[1])})"
    elif formula.type in ['FORALL', 'EXISTS']:
        quantifier = '∀' if formula.type == 'FORALL' else '∃'
        return f"{quantifier}{formula.content[0]}({formula_to_string(formula.content[1])})"
    else:
        return str(formula)


def step1_eliminate_implications(formula: Formula) -> Formula:
    if formula.type == 'IMPL':
        return Formula('OR', [Formula('NOT', [step1_eliminate_implications(formula.content[0])]),
                              step1_eliminate_implications(formula.content[1])])
    elif formula.type == 'EQUIV':
        return Formula('AND', [
            Formula('OR', [Formula('NOT', [step1_eliminate_implications(formula.content[0])]),
                           step1_eliminate_implications(formula.content[1])]),
            Formula('OR', [Formula('NOT', [step1_eliminate_implications(formula.content[1])]),
                           step1_eliminate_implications(formula.content[0])])
        ])
    elif formula.type in ['AND', 'OR']:
        return Formula(formula.type, [step1_eliminate_implications(subf) for subf in formula.content])
    elif formula.type == 'NOT':
        return Formula('NOT', [step1_eliminate_implications(formula.content[0])])
    elif formula.type in ['FORALL', 'EXISTS']:
        return Formula(formula.type, [formula.content[0], step1_eliminate_implications(formula.content[1])])
    else:
        return formula


def step2_move_negation_inwards(formula: Formula) -> Formula:
    if formula.type == 'NOT':
        inner = formula.content[0]
        if inner.type == 'AND':
            return Formula('OR', [step2_move_negation_inwards(Formula('NOT', [subf])) for subf in inner.content])
        elif inner.type == 'OR':
            return Formula('AND', [step2_move_negation_inwards(Formula('NOT', [subf])) for subf in inner.content])
        elif inner.type == 'FORALL':
            return Formula('EXISTS',
                           [inner.content[0], step2_move_negation_inwards(Formula('NOT', [inner.content[1]]))])
        elif inner.type == 'EXISTS':
            return Formula('FORALL',
                           [inner.content[0], step2_move_negation_inwards(Formula('NOT', [inner.content[1]]))])
        elif inner.type == 'NOT':
            return step2_move_negation_inwards(inner.content[0])
        else:
            return formula
    elif formula.type in ['AND', 'OR']:
        return Formula(formula.type, [step2_move_negation_inwards(subf) for subf in formula.content])
    elif formula.type in ['FORALL', 'EXISTS']:
        return Formula(formula.type, [formula.content[0], step2_move_negation_inwards(formula.content[1])])
    else:
        return formula


def step3_standardize_variables(formula: Formula, var_map: dict = None, counter: List[int] = None) -> Formula:
    if var_map is None:
        var_map = {}
    if counter is None:
        counter = [0]

    if formula.type in ['FORALL', 'EXISTS']:
        old_var = formula.content[0]
        new_var = f"x{counter[0]}"
        counter[0] += 1
        var_map[old_var] = new_var
        return Formula(formula.type, [new_var, step3_standardize_variables(formula.content[1], var_map, counter)])
    elif formula.type in ['AND', 'OR']:
        return Formula(formula.type, [step3_standardize_variables(subf, var_map, counter) for subf in formula.content])
    elif formula.type == 'PRED':
        return Formula('PRED', [formula.content[0]] + [var_map.get(arg, arg) for arg in formula.content[1:]])
    elif formula.type == 'NOT':
        return Formula('NOT', [step3_standardize_variables(formula.content[0], var_map, counter)])
    else:
        return formula


# Step 4: Skolemization
def step4_skolemize(formula: Formula, universal_vars: List[str] = None) -> Formula:
    if universal_vars is None:
        universal_vars = []

    if formula.type == 'EXISTS':
        # Replace the existentially quantified variable with a Skolem function
        skolem_func = f"f{len(universal_vars)}({','.join(universal_vars)})" if universal_vars else f"c{len(universal_vars)}"
        # Apply Skolemization and replace the existentially quantified variable
        return step4_skolemize(formula.content[1], universal_vars).replace_variable(formula.content[0], skolem_func)

    elif formula.type == 'FORALL':
        return Formula('FORALL',
                       [formula.content[0], step4_skolemize(formula.content[1], universal_vars + [formula.content[0]])])

    elif formula.type in ['AND', 'OR']:
        return Formula(formula.type, [step4_skolemize(subf, universal_vars) for subf in formula.content])

    elif formula.type == 'NOT':
        return Formula('NOT', [step4_skolemize(formula.content[0], universal_vars)])

    else:
        return formula


# Step 5: Prenex Normal Form
def step5_prenex_normal_form(formula: Formula) -> Formula:
    if formula.type in ['AND', 'OR', 'NOT']:
        return Formula(formula.type, [step5_prenex_normal_form(subf) for subf in formula.content])
    elif formula.type in ['FORALL', 'EXISTS']:
        return formula  # already in correct form
    else:
        return formula


def to_cnf(formula: Formula) -> Formula:
    """将公式转换为合取范式"""
    if formula.type == 'PRED':  # 预测符号，直接返回自己
        return formula
    elif formula.type == 'OR':  # 对“或”运算的处理
        # 对“或”运算进行递归处理
        return Formula('OR', [to_cnf(c) for c in formula.content])
    elif formula.type == 'AND':  # 对“与”运算的处理
        # 如果是 AND 连接多个子公式，递归处理每一个子公式
        return Formula('AND', [to_cnf(c) for c in formula.content])
    elif formula.type == 'FORALL':  # 对量化符号的处理
        # 对量化符号进行递归处理，量化符号不会影响 CNF 转换
        return Formula('FORALL', [formula.content[0], to_cnf(formula.content[1])])
    else:
        return formula  # 默认返回自己


# 独立的函数: 应用分配律：将 A OR (B AND C) 转换为 (A OR B) AND (A OR C)
def distribute_or_over_and(formula: Formula) -> Formula:
    """应用分配律：将 A OR (B AND C) 转换为 (A OR B) AND (A OR C)"""
    if formula.type == 'OR' and len(formula.content) == 2:
        left, right = formula.content
        if right.type == 'AND':
            # A OR (B AND C) ==> (A OR B) AND (A OR C)
            left_distributed = distribute_or_over_and(Formula('OR', [left, right.content[0]]))
            right_distributed = distribute_or_over_and(Formula('OR', [left, right.content[1]]))
            return Formula('AND', [left_distributed, right_distributed])
        else:
            return Formula('OR', [distribute_or_over_and(left), distribute_or_over_and(right)])
    elif formula.type == 'AND':
        # 如果是 AND 操作，递归处理每个子公式
        return Formula('AND', [distribute_or_over_and(c) for c in formula.content])
    elif formula.type == 'FORALL':
        # 对量化符号进行递归处理
        return Formula('FORALL', [formula.content[0], distribute_or_over_and(formula.content[1])])
    else:
        return formula


# 独立的函数: 首先递归转换成 CNF，然后应用分配律
def step6_skolem_normal_form(formula: Formula) -> Formula:
    """首先递归转换成 CNF，然后应用分配律"""
    cnf = to_cnf(formula)
    return distribute_or_over_and(cnf)


# Step 7: Drop Universal Quantifiers
def step7_drop_universal_quantifiers(formula: Formula) -> Formula:
    if formula.type == 'FORALL':
        return step7_drop_universal_quantifiers(formula.content[1])
    elif formula.type in ['AND', 'OR']:
        return Formula(formula.type, [step7_drop_universal_quantifiers(subf) for subf in formula.content])
    elif formula.type == 'NOT':
        return Formula('NOT', [step7_drop_universal_quantifiers(formula.content[0])])
    else:
        return formula


# Step 8: Conjunctive Normal Form
def flatten_and(f: Formula) -> Formula:
    # 如果是 AND，继续递归拆分，直到没有 AND 为止
    if f.type == 'AND':
        if all(subf.type != 'AND' for subf in f.content):
            return f  # 不再有 AND，返回本身
        else:
            # 否则递归拆分
            new_content = []
            for subf in f.content:
                if subf.type == 'AND':
                    # 拆开每个 AND 子公式
                    new_content.extend(flatten_and(subf).content)
                else:
                    new_content.append(subf)
            return Formula('AND', new_content)
    return f


def step8_conjunctive_normal_form(formula: Formula) -> list:
    # 然后将其中的 AND 子句完全拆分开来
    cnf = flatten_and(formula)
    # 如果是 AND 类型，返回其中的所有子句
    if cnf.type == 'AND':
        return cnf.content
    else:
        return [cnf]


# Step 9: Standardize Clause Variables
def step9_standardize_clause_variables(clauses: List[Formula]) -> List[Formula]:
    # 计数器确保变量名称唯一
    name_li = []
    for i in range(len(clauses)):
        name_li.append("x" + str(i))

    standardized_clauses = []

    # 遍历每个子句进行标准化变量替换
    for i, clause in enumerate(clauses):
        standardized_clause = standardize_variables_in_formula(clause, name_li[i])
        standardized_clauses.append(standardized_clause)

    return standardized_clauses


def standardize_variables_in_formula(formula: Formula, new_var: str) -> Formula:
    # 处理公式中的每一个元素，并替换变量
    new_content = []

    for item in formula.content:
        if isinstance(item, str):
            # 对字符串中的变量进行替换
            new_item = replace_variable(item, new_var)
            new_content.append(new_item)
        elif isinstance(item, Formula):
            # 如果是嵌套公式，递归处理
            new_content.append(standardize_variables_in_formula(item, new_var))

    return Formula(formula.type, new_content)


def replace_variable(text: str, new_var: str) -> str:
    """
    替换字符串中的变量，确保 f1(x0) 中的 x0 也能被替换。
    """
    # 替换变量 x0 为新变量
    # 匹配变量名，如 'x0' 或 'f1(x0)' 中的 'x0'
    # 不替换 'f1(x0)' 中的 f1，而是只替换其中的 'x0' 为新的变量
    return re.sub(r'\b(x\d+)\b', new_var, text)


def predicate_to_clauses(formula: Formula) -> List[Formula]:
    print("Original formula:")
    print(formula_to_string(formula))
    print()
    formula = step1_eliminate_implications(formula)
    print("Step 1 - Eliminate implications:")
    print(formula_to_string(formula))
    print()
    formula = step2_move_negation_inwards(formula)
    print("Step 2 - Move negation inwards:")
    print(formula_to_string(formula))
    print()
    formula = step3_standardize_variables(formula)
    print("Step 3 - Standardize variables:")
    print(formula_to_string(formula))
    print()
    formula = step4_skolemize(formula)
    print("Step 4 - Skolemize:")
    print(formula_to_string(formula))
    print()
    formula = step5_prenex_normal_form(formula)
    print("Step 5 - Prenex normal form:")
    print(formula_to_string(formula))
    print()
    formula = step6_skolem_normal_form(formula)  # 直接使用Skolem标准型
    print("Step 6 - Skolem normal form (CNF):")
    print(formula_to_string(formula))
    print()
    formula = step7_drop_universal_quantifiers(formula)
    print("Step 7 - Drop universal quantifiers:")
    print(formula_to_string(formula))
    print()
    clauses = step8_conjunctive_normal_form(formula)
    print("Step 8 - Conjunctive normal form:")
    for clause in clauses:
        print(formula_to_string(clause))
    print()
    clauses = step9_standardize_clause_variables(clauses)
    print("Step 9 - Standardize clause variables:")
    for clause in clauses:
        print(formula_to_string(clause))
    print()
    return clauses


# 示例使用
if __name__ == "__main__":
    # 示例公式: ∀x(¬P(x) ↔ ∃y(Q(x,y) ∧ R(y)))   IMPL
    example_formula = Formula('FORALL', ['x', Formula('EQUIV', [
        Formula('NOT', [Formula('PRED', ['P', 'x'])]),
        Formula('EXISTS', ['y', Formula('AND', [
            Formula('PRED', ['Q', 'x', 'y']),
            Formula('PRED', ['R', 'y'])
        ])])
    ])])
    result = predicate_to_clauses(example_formula)
    print("Final resulting clauses:")
    for clause in result:
        print(formula_to_string(clause))
