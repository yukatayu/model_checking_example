use std::{collections::HashMap, collections::HashSet};
use itertools::iproduct;

enum MemoryAddressElement {
    Pid,
    Opid,
}

enum ImmediateValue {
    Pid,
    Opid,
    Val(bool)
}

type MemoryAddress = (&'static str, Option<MemoryAddressElement>);

struct SetValue {
    target: MemoryAddress,
    value: ImmediateValue
}

struct GotoIf {
    target: MemoryAddress,
    value: ImmediateValue,
    goto_then: i32,
    goto_else: i32
}

enum Statement{
    SetValueStat(SetValue),
    GotoIfStat(GotoIf)
}

fn main() {
    use MemoryAddressElement::{Pid, Opid};
    use ImmediateValue::Val;
    use Statement::{SetValueStat, GotoIfStat};
    let program1 = vec![
        SetValueStat( SetValue{ target: ("b", Some(Pid)),  value: ImmediateValue::Val(true) } ),
        GotoIfStat  ( GotoIf  { target: ("turn", None),    value: ImmediateValue::Pid, goto_then: 2, goto_else: 4 } ),
        GotoIfStat  ( GotoIf  { target: ("b", Some(Opid)), value: Val(true),           goto_then: 2, goto_else: 3 } ),
        SetValueStat( SetValue{ target: ("turn", None),    value: ImmediateValue::Pid } ),
        SetValueStat( SetValue{ target: ("c", Some(Pid)),  value: Val(true)  } ),
        SetValueStat( SetValue{ target: ("c", Some(Pid)),  value: Val(false) } ),
        SetValueStat( SetValue{ target: ("b", Some(Pid)),  value: Val(false) } ),
    ];

    let program2 = vec![
        SetValueStat( SetValue{ target: ("b", Some(Pid)),  value: ImmediateValue::Val(true) } ),
        SetValueStat( SetValue{ target: ("turn", None),    value: ImmediateValue::Opid } ),
        GotoIfStat  ( GotoIf  { target: ("b", Some(Opid)), value: Val(true),            goto_then: 3, goto_else: 4 } ),
        GotoIfStat  ( GotoIf  { target: ("turn", None),    value: ImmediateValue::Opid, goto_then: 2, goto_else: 4 } ),
        SetValueStat( SetValue{ target: ("c", Some(Pid)),  value: Val(true)  } ),
        SetValueStat( SetValue{ target: ("c", Some(Pid)),  value: Val(false) } ),
        SetValueStat( SetValue{ target: ("b", Some(Pid)),  value: Val(false) } ),
    ];

    let label_list = vec![("b",true), ("turn", false), ("c", true)];
    // generate_relation_for_pair_processes(&program1, &label_list);

    
    let program3 = vec![
        SetValueStat( SetValue{ target: ("c", None),  value: ImmediateValue::Val(true) } ),
        GotoIfStat  ( GotoIf  { target: ("c", None),  value: ImmediateValue::Pid, goto_then: 0, goto_else: 1 } ),
    ];
    let label_list_3 = vec![("c", false)];
    generate_relation_for_pair_processes(&program3, &label_list_3);

    // A G not(c[0], c[1])
}

fn generate_relation_for_pair_processes(program: &Vec<Statement>, label_list: &Vec<(&'static str, bool)>) {
    // パラメータの列挙
    let (param_map, param_count) =
    {
        let mut param_list: Vec<((&'static str, Option<bool>), i32)> = Vec::new();
        let mut used_param_count = 0;
        for label in label_list.iter(){
            let (name, is_array) = label;
            if *is_array {
                param_list.push(((name, Some(true)),  used_param_count)); used_param_count += 1;
                param_list.push(((name, Some(false)), used_param_count)); used_param_count += 1;
            } else {
                param_list.push(((name, None),        used_param_count)); used_param_count += 1;
            }
        }
        (param_list.into_iter().collect::<HashMap<_, _>>(), used_param_count)
    };

    // 全状態の列挙
    type Status = (Vec<i32>, Vec<bool>);  // プログラムをどこまで実行したか， 状態
    fn generate_all_status(target: &mut Vec<Status>, proc_status: &Vec<i32>, depth_left: i32, current_vec: Vec<bool>) {
        if depth_left <= 0 {
            let new_proc_status = proc_status.clone();
            target.push((new_proc_status, current_vec));
        } else {
            let mut new_vec    = current_vec.clone(); new_vec.push(false);
            generate_all_status(target, proc_status, depth_left - 1, new_vec);

            let mut new_vec    = current_vec.clone(); new_vec.push(true);
            generate_all_status(target, proc_status, depth_left - 1, new_vec);
        };
    }

    let mut status_list: Vec<Status> = Vec::new();
    for (proc1, proc2) in iproduct!(0..(program.len()+1) as i32, 0..(program.len()+1) as i32) {
        let proc_status = vec![proc1, proc2];
        generate_all_status(&mut status_list, &proc_status, param_count, vec![]);
    }

    // グラフの構築
    let mut transition_list: HashMap<Status, HashSet<Status>> = HashMap::new();
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

                    fn interpret_address(address: &MemoryAddress, pid: bool, opid: bool) -> (&'static str, Option<bool>) {
                        (address.0, match address.1 {
                            None => None,
                            Some(MemoryAddressElement::Pid) => Some(pid),
                            Some(MemoryAddressElement::Opid) => Some(opid)
                        })
                    }
                    fn interpret_value(value: &ImmediateValue, pid: bool, opid: bool) -> bool {
                        match value {
                            ImmediateValue::Pid => pid,
                            ImmediateValue::Opid => opid,
                            ImmediateValue::Val(val) => *val
                        }
                    }

                    match &program[line as usize] {
                        Statement::GotoIfStat  (statement) => {
                            let interpreted_address = interpret_address(&statement.target, pid, opid);
                            let target = param_list[*param_map.get(&interpreted_address).unwrap() as usize];
                            let value = interpret_value(&statement.value, pid, opid);
                            if target == value {
                                next_proc_status[pid_i] = statement.goto_then;
                            } else {
                                next_proc_status[pid_i] = statement.goto_else;
                            };
                        },
                        Statement::SetValueStat(statement) => {
                            let interpreted_address = interpret_address(&statement.target, pid, opid);
                            let value = interpret_value(&statement.value, pid, opid);
                            next_param_list[*param_map.get(&interpreted_address).unwrap() as usize] = value;
                        }
                    }

                    let next_status = (next_proc_status, next_param_list);
                    transition_list.entry(status.clone()).or_insert(HashSet::new());
                    transition_list.get_mut(status).unwrap().insert(next_status);
                }
            }
        }
    };
    // println!("{:#?}", transition_list);
    println!("{:?}", transition_list);
    // (param_map, param_count, status_list, transition_list, )



    // ([0,0],[0,0,0,0,0,0,0])
    // ......
    // ([7,7],[1,1,1,1,1,1,1])


    
    // paramList = {
    //     ("b", 0),("b", 1),("turn",None),("c",0),("c",1),
    // }
    // statusList = 2^paramList * [0, |program|] * [0, |program|]

    // Map<statusList , (predicate, aims_to: Vec<status> )>
}
