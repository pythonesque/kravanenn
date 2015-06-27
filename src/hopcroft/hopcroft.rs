use std::cmp::{Ord, Ordering};
use std::vec::Vec;
use hopcroft::partition::{Partition, Set};

type state = usize;

pub struct Transition<L> {
  lbl : L,
  src : state,
  dst : state,
}

pub struct Automaton<L> {
  /// Number of states
  states : usize,
  /// List of unique transitions between states
  transitions : Box<[Transition<L>]>,
}

pub trait Hopcroft<T> {

/// Associate the equivalence classes of the states of an automaton
fn reduce (a : &mut Automaton<T>) -> Partition;

}

struct Environment {
  /// Current partition of the states
  state_partition : Partition,
  /// Current partition of the transitions
  transition_partition : Partition,
  /// Associate to each transition its source
  transition_source : Box<[usize]>,
  /// Associate to each state the list of transitions that ends in it
  state_pred_trans : Box<[Vec<usize>]>,
  /// Partitions waiting to be processed
  partition_todo : Vec<Set>,
}

/// Associate the list of transitions ending in a given state
fn reverse<T>(automaton : &Automaton<T>) -> Box<[Vec<usize>]> {
  let mut ans = Vec::with_capacity(automaton.states);
  for _ in 0..automaton.states {
    ans.push(Vec::new());
  }
  let mut ans = ans.into_boxed_slice();
  let mut i : usize = 0;
  for trans in automaton.transitions.into_iter() {
    ans[trans.dst].push(i);
    i = i + 1;
  }
  ans
}

fn init<T : Ord>(automaton : &mut Automaton<T>) -> Environment {
  // Sort transitions according to their label
  automaton.transitions.sort_by(|x, y| { Ord::cmp(&(x.lbl), &(y.lbl)) });
  // Initialize the environment
  let len = automaton.transitions.len();
  let st_part = Partition::new(automaton.states);
  let mut sp_part = Partition::new(len);
  let mut trans_src = Vec::with_capacity(len);
  // Set the source of the transitions
  for i in 0..len { trans_src.push(automaton.transitions[i].src) }
  let trans_src = trans_src.into_boxed_slice();
  // Split splitters according to their label
  if len > 0 {
    let mut label0 = &(automaton.transitions[0].lbl);
    // pt is initial, full partition
    let pt = sp_part.partition(0);
    for i in 0..len {
      // Each time the label changes, we split
      let label = &(automaton.transitions[i].lbl);
      let _ = match Ord::cmp(label, label0) {
        Ordering::Equal => {}
        _ => {
          let _ = sp_part.split(pt);
          label0 = label;
        }
      };
      sp_part.mark(i);
    }
    let _ = sp_part.split(pt);
  }
  // Push every splitter in the todo stack
  let mut todo = Vec::new();
  for partition in sp_part.into_iter() {
    todo.push(partition);
  }
  Environment {
    state_partition : st_part,
    transition_partition : sp_part,
    transition_source : trans_src,
    state_pred_trans : reverse(automaton),
    partition_todo : todo,
  }
}

fn split_partition(s : Set, env : &mut Environment) {
  let r = match env.state_partition.split(s) {
    None => { return; }
    Some (r) => { r }
  };
  let ref state_part = env.state_partition;
  let ref state_pred_trans = env.state_pred_trans;
  let ref mut trans_part = env.transition_partition;
  let r = if state_part.size(r) < state_part.size(s) { r } else { s };
//   let _ = state_part.class(r).flat_map(|state| {
//     let ref preds : Vec<usize> = state_pred_trans[state];
//     preds.into_iter().filter(|trans : &&usize| {
//       let pt = trans_part.partition(**trans); 
//       let ans = trans_part.is_marked(pt);
//       trans_part.mark(**trans);
//       ans
//     })
//   });
  ()
}

// let split_partition s inv env todo =
//   let p = env.state_partition in
//   let r = SPartition.split s p in
//   if SPartition.is_valid r then begin
//     let r = if SPartition.size r p < SPartition.size s p then r else s in
//     let fold state accu =
//       let fold accu trans =
//         let pt = TPartition.partition trans env.transition_partition in
//         let accu =
//           if TPartition.is_marked pt env.transition_partition then accu
//           else pt :: accu
//         in
//         let () = TPartition.mark trans env.transition_partition in
//         accu
//       in
//       List.fold_left fold accu inv.(state)
//     in
//     let splitter_touched = SPartition.fold r fold p [] in
//     let fold_touched todo pt =
//       let npt = TPartition.split pt env.transition_partition in
//       if TPartition.is_valid npt then npt :: todo
//       else todo
//     in
//     List.fold_left fold_touched todo splitter_touched
//   end else
//     todo
// 
// let reduce_aux automaton =
//   let env, splitter_todo = init automaton in
//   let inv = reverse automaton in
//   let rec loop = function
//   | [] -> ()
//   | pt :: todo ->
//     let fold t state_touched =
//       let previous = env.transition_source.(t) in
//       let equiv = SPartition.partition previous env.state_partition in
//       let state_touched =
//         if SPartition.is_marked equiv env.state_partition then state_touched
//         else equiv :: state_touched
//       in
//       let () = SPartition.mark previous env.state_partition in
//       state_touched
//     in
//     let state_touched = TPartition.fold pt fold env.transition_partition [] in
//     let fold_touched todo equiv = split_partition equiv inv env todo in
//     let splitter_todo = List.fold_left fold_touched todo state_touched in
//     loop splitter_todo
//   in
//   let () = loop splitter_todo in
//   (env, inv)
// 
// let reduce automaton =
//   let (ans, _) = reduce_aux automaton in
//   let mapping = Array.create (SPartition.length ans.state_partition) [] in
//   let iter set =
//     let pi = SPartition.represent set in
//     let iter i =
//       let map = Array.unsafe_get mapping pi in
//       Array.unsafe_set mapping pi (i :: map)
//     in
//     SPartition.iter set iter ans.state_partition
//   in
//   let () = SPartition.iter_all iter ans.state_partition in
//   mapping
// 
//   let reduce_partition automaton =
//     let (ans, _) = reduce_aux automaton in
//     ans.state_partition
// 
// end

impl<T> Hopcroft<T> for T where T : Ord {

fn reduce (automaton : &mut Automaton<T>) -> Partition {
  let env = init(automaton);
  panic!("foo");
}

}