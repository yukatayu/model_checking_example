use indoc::indoc;
use itertools::iproduct;
use itertools::Itertools;
use std::fmt::Formatter;
use std::{collections::HashMap, collections::HashSet};

// 検査対象のプログラムを表現するための構造体たち
enum MemoryAddressElement {
    Pid,
    Opid,
}

impl std::fmt::Display for MemoryAddressElement {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                MemoryAddressElement::Pid => "pid".to_string(),
                MemoryAddressElement::Opid => "1-pid".to_string(),
            }
        )
    }
}

enum ImmediateValue {
    Pid,
    Opid,
    Val(bool),
}

impl std::fmt::Display for ImmediateValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                ImmediateValue::Pid => "pid".to_string(),
                ImmediateValue::Opid => "1-pid".to_string(),
                ImmediateValue::Val(b) => b.to_string(),
            }
        )
    }
}

struct MemoryAddress(&'static str, Option<MemoryAddressElement>);

impl From<(&'static str, Option<MemoryAddressElement>)> for MemoryAddress {
    fn from(pair: (&'static str, Option<MemoryAddressElement>)) -> Self {
        MemoryAddress(pair.0, pair.1)
    }
}

impl std::fmt::Display for MemoryAddress {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}",
            self.0,
            self.1
                .as_ref()
                .map_or_else(|| "".to_string(), |index| format!("{}", index))
        )
    }
}

struct SetValue {
    target: MemoryAddress,
    value: ImmediateValue,
}

struct GotoIf {
    target: MemoryAddress,
    value: ImmediateValue,
    goto_then: i32,
    goto_else: i32,
}

enum Statement {
    SetValueStat(SetValue),
    GotoIfStat(GotoIf),
}

impl std::fmt::Display for Statement {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Statement::SetValueStat(s) => {
                    format!("{} = {}", &s.target, &s.value)
                }
                Statement::GotoIfStat(s) => {
                    format!(
                        "if({} = {}){{ goto {} }}else{{ goto {} }}",
                        &s.target, &s.value, s.goto_then, s.goto_else
                    )
                }
            }
        )
    }
}

// 検査する式を表現するための構造体たち
type ProgramStatus = (Vec<i32>, Vec<bool>); // プログラムをどこまで実行したか， 状態

type TransitionMap = HashMap<(Vec<i32>, Vec<bool>), HashSet<(Vec<i32>, Vec<bool>)>>;

#[allow(dead_code)]
struct KripkeStructure {
    param_map: HashMap<(&'static str, Option<bool>), i32>,
    param_count: i32,
    status_list: Vec<(Vec<i32>, Vec<bool>)>,
    transition: TransitionMap,
    rev_transition: TransitionMap,
}

struct Proposition {
    address: (&'static str, Option<bool>),
}

#[allow(dead_code)]
enum SyntaxTree {
    Literal(Proposition),
    And((Box<SyntaxTree>, Box<SyntaxTree>)),
    Or((Box<SyntaxTree>, Box<SyntaxTree>)),
    Not(Box<SyntaxTree>),
    AG(Box<SyntaxTree>),
}

impl std::fmt::Display for SyntaxTree {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                SyntaxTree::Literal(prop) => {
                    let (name, index) = prop.address;
                    index.as_ref().map_or_else(
                        || format!("{}", name),
                        |x| format!("{}[{}]", name, *x as i32),
                    )
                }
                SyntaxTree::And((y, x)) => {
                    format!("({} \u{2227} {}", &*y, &*x)
                }
                SyntaxTree::Or((y, x)) => {
                    format!("({} \u{2228} {}", &*y, &*x)
                }
                SyntaxTree::Not(x) => {
                    format!("\u{ffe2}{}", &*x) // ￢
                }
                SyntaxTree::AG(x) => {
                    format!("\u{2200}\u{25a1} {}", &*x) // AG,
                } // TODO: F → \u{25c7}, N → \u{25cb}
            }
        )
    }
}

fn main() {
    use ImmediateValue::Val;
    use MemoryAddressElement::{Opid, Pid};
    use Statement::{GotoIfStat, SetValueStat};
    let program1 = vec![
        SetValueStat(SetValue {
            target: ("b", Some(Pid)).into(),
            value: ImmediateValue::Val(true),
        }),
        GotoIfStat(GotoIf {
            target: ("turn", None).into(),
            value: ImmediateValue::Opid,
            goto_then: 2,
            goto_else: 4,
        }),
        GotoIfStat(GotoIf {
            target: ("b", Some(Opid)).into(),
            value: Val(true),
            goto_then: 2,
            goto_else: 3,
        }),
        SetValueStat(SetValue {
            target: ("turn", None).into(),
            value: ImmediateValue::Pid,
        }),
        SetValueStat(SetValue {
            target: ("c", Some(Pid)).into(),
            value: Val(true),
        }),
        SetValueStat(SetValue {
            target: ("c", Some(Pid)).into(),
            value: Val(false),
        }),
        SetValueStat(SetValue {
            target: ("b", Some(Pid)).into(),
            value: Val(false),
        }),
    ];

    let program2 = vec![
        SetValueStat(SetValue {
            target: ("b", Some(Pid)).into(),
            value: ImmediateValue::Val(true),
        }),
        SetValueStat(SetValue {
            target: ("turn", None).into(),
            value: ImmediateValue::Opid,
        }),
        GotoIfStat(GotoIf {
            target: ("b", Some(Opid)).into(),
            value: Val(true),
            goto_then: 3,
            goto_else: 4,
        }),
        GotoIfStat(GotoIf {
            target: ("turn", None).into(),
            value: ImmediateValue::Opid,
            goto_then: 2,
            goto_else: 4,
        }),
        SetValueStat(SetValue {
            target: ("c", Some(Pid)).into(),
            value: Val(true),
        }),
        SetValueStat(SetValue {
            target: ("c", Some(Pid)).into(),
            value: Val(false),
        }),
        SetValueStat(SetValue {
            target: ("b", Some(Pid)).into(),
            value: Val(false),
        }),
    ];

    let initial_set = vec![(vec![0, 0], vec![false, false, false, false, false])]
        .into_iter()
        .collect::<HashSet<_>>();
    let label_list = vec![("b", true), ("turn", false), ("c", true)];

    // A G not(c[0] and c[1]) を検査したい
    let is_sound = SyntaxTree::AG(Box::new(SyntaxTree::Not(Box::new(SyntaxTree::And((
        Box::new(SyntaxTree::Literal(Proposition {
            address: ("c", Some(false)),
        })),
        Box::new(SyntaxTree::Literal(Proposition {
            address: ("c", Some(true)),
        })),
    ))))));

    let check_formulae = vec![is_sound];
    for (program, program_name) in vec![(program1, "A"), (program2, "B")] {
        println!(
            indoc! {r#"

            [{name}]
            ----------
            {program}
            ----------
        "#},
            name = program_name,
            program = program
                .iter()
                .enumerate()
                .map(|(line, stmt)| format!("{} | {}", line, stmt))
                .join("\n")
        );

        let kripke_structure = kripke_structure_for_pair_processes(&program, &label_list);
        for formula in check_formulae.iter() {
            let sat_set = sat_set_of(&kripke_structure, formula);
            let counter_example = &initial_set - &sat_set;
            print!("  {}", formula);
            if counter_example.is_empty() {
                println!(" : OK!")
            } else {
                println!(" : Error!\n    → {:?}", counter_example);
            }
        }
    }
}

fn sat_set_of(kripke_structure: &KripkeStructure, formula: &SyntaxTree) -> HashSet<ProgramStatus> {
    match &formula {
        SyntaxTree::Literal(prop) => {
            let param_pos = *kripke_structure.param_map.get(&prop.address).unwrap();
            kripke_structure
                .status_list
                .iter()
                .cloned()
                .filter(|program_status| {
                    let (_, status) = program_status;
                    *status.get(param_pos as usize).unwrap()
                })
                .collect::<HashSet<_>>()
        }
        SyntaxTree::And((y, x)) => {
            let lhs = sat_set_of(kripke_structure, &*y);
            let rhs = sat_set_of(kripke_structure, &*x);
            &lhs & &rhs
        }
        SyntaxTree::Or((y, x)) => {
            let lhs = sat_set_of(kripke_structure, &*y);
            let rhs = sat_set_of(kripke_structure, &*x);
            &lhs | &rhs
        }
        SyntaxTree::Not(x) => {
            let rhs = sat_set_of(kripke_structure, &*x);
            let all = kripke_structure
                .status_list
                .iter()
                .cloned()
                .collect::<HashSet<_>>();
            &all - &rhs
        }
        &SyntaxTree::AG(x) => {
            let rhs = sat_set_of(kripke_structure, &*x);

            let ag = |status: &ProgramStatus| -> bool {
                let mut bfs_candidate: HashSet<ProgramStatus> = HashSet::new();
                let mut visited: HashSet<ProgramStatus> = HashSet::new();
                bfs_candidate.insert(status.clone());
                while !bfs_candidate.is_empty() {
                    let top = bfs_candidate.iter().cloned().next().unwrap();
                    if rhs.get(&top) == None {
                        return false;
                    }
                    if let Some(trans) = kripke_structure.transition.get(&top) {
                        for status in trans.iter() {
                            if visited.get(status) == None {
                                bfs_candidate.insert(status.clone());
                                visited.insert(status.clone());
                            }
                        }
                    }
                    bfs_candidate.remove(&top);
                }
                true
            };

            kripke_structure
                .status_list
                .iter()
                .cloned()
                .filter(|program_status| ag(program_status))
                .collect::<HashSet<_>>()
        }
    }
}

fn kripke_structure_for_pair_processes(
    program: &[Statement],
    label_list: &[(&'static str, bool)],
) -> KripkeStructure {
    // パラメータの列挙
    let (param_map, param_count) = {
        let mut param_list: Vec<((&'static str, Option<bool>), i32)> = Vec::new();
        let mut used_param_count = 0;
        for label in label_list.iter() {
            let (name, is_array) = label;
            if *is_array {
                param_list.push(((name, Some(true)), used_param_count));
                used_param_count += 1;
                param_list.push(((name, Some(false)), used_param_count));
                used_param_count += 1;
            } else {
                param_list.push(((name, None), used_param_count));
                used_param_count += 1;
            }
        }
        (
            param_list.into_iter().collect::<HashMap<_, _>>(),
            used_param_count,
        )
    };

    // 全状態の列挙
    let mut status_list: Vec<ProgramStatus> = Vec::new();
    for (proc1, proc2) in iproduct!(0..(program.len() + 1) as i32, 0..(program.len() + 1) as i32) {
        let proc_status = vec![proc1, proc2];
        status_list.append(
            &mut std::iter::repeat(())
                .take(param_count as usize)
                .map(|_| (0..=1))
                .multi_cartesian_product()
                .into_iter()
                .map(|state| {
                    (
                        proc_status.clone(),
                        state.into_iter().map(|val| val != 0).collect::<Vec<_>>(),
                    )
                })
                .collect::<Vec<_>>(),
        );
    }

    // グラフの構築
    let mut transition: HashMap<ProgramStatus, HashSet<ProgramStatus>> = HashMap::new();
    let mut rev_transition: HashMap<ProgramStatus, HashSet<ProgramStatus>> = HashMap::new();
    for pid_i in 0..2 {
        for line in 0..program.len() as i32 {
            for status in status_list.iter() {
                let (proc_status, param_list) = status;
                if proc_status[pid_i] == line {
                    let pid = pid_i == 1;
                    let opid = !pid;

                    let mut next_proc_status = proc_status.clone();
                    next_proc_status[pid_i] += 1;

                    let mut next_param_list = param_list.clone();

                    fn interpret_address(
                        address: &MemoryAddress,
                        pid: bool,
                        opid: bool,
                    ) -> (&'static str, Option<bool>) {
                        (
                            address.0,
                            match address.1 {
                                None => None,
                                Some(MemoryAddressElement::Pid) => Some(pid),
                                Some(MemoryAddressElement::Opid) => Some(opid),
                            },
                        )
                    }
                    fn interpret_value(value: &ImmediateValue, pid: bool, opid: bool) -> bool {
                        match value {
                            ImmediateValue::Pid => pid,
                            ImmediateValue::Opid => opid,
                            ImmediateValue::Val(val) => *val,
                        }
                    }

                    match &program[line as usize] {
                        Statement::GotoIfStat(statement) => {
                            let interpreted_address =
                                interpret_address(&statement.target, pid, opid);
                            let target =
                                param_list[*param_map.get(&interpreted_address).unwrap() as usize];
                            let value = interpret_value(&statement.value, pid, opid);
                            if target == value {
                                next_proc_status[pid_i] = statement.goto_then;
                            } else {
                                next_proc_status[pid_i] = statement.goto_else;
                            };
                        }
                        Statement::SetValueStat(statement) => {
                            let interpreted_address =
                                interpret_address(&statement.target, pid, opid);
                            let value = interpret_value(&statement.value, pid, opid);
                            next_param_list
                                [*param_map.get(&interpreted_address).unwrap() as usize] = value;
                        }
                    }

                    let next_status = (next_proc_status, next_param_list);

                    transition
                        .entry(status.clone())
                        .or_insert_with(HashSet::new)
                        .insert(next_status.clone());

                    rev_transition
                        .entry(next_status.clone())
                        .or_insert_with(HashSet::new)
                        .insert(status.clone());
                }
            }
        }
    }
    // println!("{:?}", transition);
    KripkeStructure {
        param_map,
        param_count,
        status_list,
        transition,
        rev_transition,
    }
}
