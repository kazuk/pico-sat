use crate::{solver::Variable, Literal, Variables};
use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet},
    fmt::Display,
    ops::Deref,
};
use tracing::trace;

/// boolean expression node
#[derive(Debug, PartialEq, Clone, Eq)]
pub enum Node {
    /// Literal, references SAT variable
    Literal(Variable, bool),
    /// And, true if all Node is true
    And(Vec<Node>),
    /// Or, true if any Node is true
    Or(Vec<Node>),
    /// Node, true if Node is false
    Not(Box<Node>),
    /// False, false is never True Node : example And( X, Not(X) )
    False,
    /// True, true is always True : example Or(X, Not(X))
    True,
}

impl Ord for Node {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl PartialOrd for Node {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Node::Literal(v1, d1), Node::Literal(v2, d2)) => {
                match v1.index().partial_cmp(&v2.index()) {
                    Some(Ordering::Equal) => d1.partial_cmp(d2),
                    r => r,
                }
            }
            (Node::And(items1), Node::And(items2)) => {
                let items1 = items1.deref();
                let items2 = items2.deref();
                let comp_len = items1.len().min(items2.len());
                for index in 0..comp_len {
                    match items1[index].partial_cmp(&items2[index]) {
                        Some(Ordering::Equal) => continue,
                        Some(Ordering::Greater) => return Some(Ordering::Greater),
                        Some(Ordering::Less) => return Some(Ordering::Less),
                        None => return None,
                    }
                }
                if items1.len() == items2.len() {
                    return Some(Ordering::Equal);
                }
                if items1.len() > items2.len() {
                    Some(Ordering::Greater)
                } else {
                    Some(Ordering::Less)
                }
            }
            (Node::Or(items1), Node::Or(items2)) => {
                let items1 = items1.deref();
                let items2 = items2.deref();
                let comp_len = items1.len().min(items2.len());
                for index in 0..comp_len {
                    match items1[index].partial_cmp(&items2[index]) {
                        Some(Ordering::Equal) => continue,
                        Some(Ordering::Greater) => return Some(Ordering::Greater),
                        Some(Ordering::Less) => return Some(Ordering::Less),
                        None => return None,
                    }
                }
                if items1.len() == items2.len() {
                    return Some(Ordering::Equal);
                }
                if items1.len() > items2.len() {
                    Some(Ordering::Greater)
                } else {
                    Some(Ordering::Less)
                }
            }
            (Node::Not(item1), Node::Not(item2)) => item1.deref().partial_cmp(item2.deref()),
            (Node::Literal(_, _), Node::And(_)) => Some(Ordering::Less),
            (Node::Literal(_, _), Node::Or(_)) => Some(Ordering::Less),
            (Node::Literal(_, _), Node::Not(_)) => Some(Ordering::Less),
            (Node::And(_), Node::Literal(_, _)) => Some(Ordering::Greater),
            (Node::And(_), Node::Or(_)) => Some(Ordering::Less),
            (Node::And(_), Node::Not(_)) => Some(Ordering::Greater),
            (Node::Or(_), Node::Literal(_, _)) => Some(Ordering::Less),
            (Node::Or(_), Node::And(_)) => Some(Ordering::Less),
            (Node::Or(_), Node::Not(_)) => Some(Ordering::Greater),
            (Node::Not(_), Node::Literal(_, _)) => Some(Ordering::Less),
            (Node::Not(_), Node::And(_)) => Some(Ordering::Less),
            (Node::Not(_), Node::Or(_)) => Some(Ordering::Less),
            (Node::Literal(_, _), Node::False) => Some(Ordering::Less),
            (Node::Literal(_, _), Node::True) => Some(Ordering::Less),
            (Node::And(_), Node::False) => Some(Ordering::Less),
            (Node::And(_), Node::True) => Some(Ordering::Less),
            (Node::Or(_), Node::False) => Some(Ordering::Less),
            (Node::Or(_), Node::True) => Some(Ordering::Less),
            (Node::Not(_), Node::False) => Some(Ordering::Less),
            (Node::Not(_), Node::True) => Some(Ordering::Less),
            (Node::False, Node::Literal(_, _)) => Some(Ordering::Greater),
            (Node::False, Node::And(_)) => Some(Ordering::Greater),
            (Node::False, Node::Or(_)) => Some(Ordering::Greater),
            (Node::False, Node::Not(_)) => Some(Ordering::Greater),
            (Node::False, Node::False) => Some(Ordering::Equal),
            (Node::False, Node::True) => Some(Ordering::Less),
            (Node::True, Node::Literal(_, _)) => Some(Ordering::Greater),
            (Node::True, Node::And(_)) => Some(Ordering::Greater),
            (Node::True, Node::Or(_)) => Some(Ordering::Greater),
            (Node::True, Node::Not(_)) => Some(Ordering::Greater),
            (Node::True, Node::False) => Some(Ordering::Greater),
            (Node::True, Node::True) => Some(Ordering::Equal),
        }
    }
}

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            Node::Literal(v, d) => match d {
                true => write!(f, "[{}]", v.index())?,
                false => write!(f, "[~{}]", v.index())?,
            },
            Node::And(items) => {
                let mut first = true;
                write!(f, "(")?;
                for item in (*items).iter() {
                    if !first {
                        write!(f, "&&")?;
                    };
                    write!(f, "{}", item)?;
                    first = false;
                }
                write!(f, ")")?;
            }
            Node::Or(items) => {
                let mut first = true;
                write!(f, "(")?;
                for item in (*items).iter() {
                    if !first {
                        write!(f, "||")?;
                    };
                    write!(f, "{}", item)?;
                    first = false;
                }
                write!(f, ")")?;
            }
            Node::Not(item) => {
                write!(f, "!({})", *item)?;
            }
            Node::True => {
                write!(f, "T")?;
            }
            Node::False => {
                write!(f, "F")?;
            }
        }
        Ok(())
    }
}

impl Node {
    /// convert Node to Solver input (Conjective Normal Foam)
    #[tracing::instrument]
    pub fn to_cnf(&self, vars: &mut Variables) -> Vec<Vec<Literal>> {
        trace!("to_cnf");

        // converts Literal node or Not Literal node to solver Literal
        fn to_literal(node: Node) -> Literal {
            match node {
                Node::And(_) => panic!("to_literal on AND"),
                Node::Or(_) => panic!("to_literal on OR"),
                Node::Literal(lit, v) => {
                    if v {
                        lit.t()
                    } else {
                        lit.f()
                    }
                }
                Node::Not(boxed) => match *boxed {
                    Node::Literal(lit, v) => {
                        if v {
                            lit.f()
                        } else {
                            lit.t()
                        }
                    }
                    _ => panic!("unexpected node format {:?}", boxed),
                },
                Node::True => {
                    panic!("TRUE to literal");
                }
                Node::False => {
                    panic!("FALSE to literal");
                }
            }
        }

        // recursive get single or-literal
        fn to_literals(node: Node) -> Vec<Literal> {
            match node {
                Node::And(_) => panic!("to_literals on AND"),
                Node::Or(items) => {
                    let mut result = Vec::new();
                    for item in items {
                        match item {
                            Node::And(_) => panic!("to_literals on AND content"),
                            Node::Or(_) => result.append(&mut to_literals(item)),
                            Node::Literal(_, _) | Node::Not(_) => result.push(to_literal(item)),
                            Node::True | Node::False => panic!("to_literals on TRUE/FALSE"),
                        }
                    }
                    result
                }
                Node::Literal(_, _) | Node::Not(_) => {
                    vec![to_literal(node)]
                }
                Node::True | Node::False => panic!("to_literals on TRUE/FALSE"),
            }
        }

        // recursive get or-literals
        fn collect_literals(node: Node) -> Vec<Vec<Literal>> {
            match node {
                Node::And(items) => {
                    let mut result = Vec::new();
                    for item in items {
                        result.append(&mut collect_literals(item))
                    }
                    result
                }
                Node::Or(_) | Node::Literal(_, _) | Node::Not(_) => vec![to_literals(node)],
                Node::True | Node::False => panic!("collect_literals on TRUE/FALSE"),
            }
        }

        let aon = self.to_and_or_not_form(vars);
        collect_literals(aon)
    }

    /// convert Node to Disjunctive normal form
    #[tracing::instrument]
    pub fn to_dnf(&self) -> Vec<Vec<Literal>> {
        // converts Literal node or Not Literal node to solver Literal
        fn to_literal(node: Node) -> Literal {
            match node {
                Node::And(_) => panic!("to_literal on AND"),
                Node::Or(_) => panic!("to_literal on OR"),
                Node::Literal(lit, v) => {
                    if v {
                        lit.t()
                    } else {
                        lit.f()
                    }
                }
                Node::Not(boxed) => match *boxed {
                    Node::Literal(lit, v) => {
                        if v {
                            lit.f()
                        } else {
                            lit.t()
                        }
                    }
                    _ => panic!("unexpected node format {:?}", boxed),
                },
                Node::True | Node::False => panic!("to_literal on TRUE/FALSE"),
            }
        }

        // recursive get single and-literal
        fn to_literals(node: Node) -> Vec<Literal> {
            match node {
                Node::Or(_) => panic!("to_literals on OR"),
                Node::And(items) => {
                    let mut result = Vec::new();
                    for item in items {
                        match item {
                            Node::Or(_) => panic!("to_literals on OR content"),
                            Node::And(_) => result.append(&mut to_literals(item)),
                            Node::Literal(_, _) | Node::Not(_) => result.push(to_literal(item)),
                            Node::True | Node::False => panic!("to_literals on TRUE/FALSE"),
                        }
                    }
                    result
                }
                Node::Literal(_, _) | Node::Not(_) => {
                    vec![to_literal(node)]
                }
                Node::True | Node::False => panic!("to_literals on TRUE/FALSE"),
            }
        }

        // recursive get and-literals
        fn collect_literals(node: Node) -> Vec<Vec<Literal>> {
            match node {
                Node::Or(items) => {
                    let mut result = Vec::new();
                    for item in items {
                        result.append(&mut collect_literals(item))
                    }
                    result
                }
                Node::And(_) | Node::Literal(_, _) | Node::Not(_) => vec![to_literals(node)],
                Node::True | Node::False => panic!("collect_literals on TRUE/FALSE"),
            }
        }

        let oan = self.to_or_and_not_form();
        collect_literals(oan)
    }

    #[tracing::instrument]
    fn is_false(&self) -> bool {
        matches!(self, Node::False)
    }

    #[tracing::instrument]
    fn is_true(&self) -> bool {
        matches!(self, Node::True)
    }

    // return v from Literal(v) or Not(Liteal(v))
    #[tracing::instrument]
    fn index(&self) -> Option<u32> {
        match self {
            Node::Literal(v, _) => Some(v.index()),
            Node::Not(child) => match child.deref() {
                Node::Literal(v, _) => Some(v.index()),
                _ => None,
            },
            _ => None,
        }
    }

    /// referenced valiables under self
    pub fn reference_variables(&self) -> HashSet<Variable> {
        match self {
            Node::Literal(v, _) => {
                let mut result = HashSet::new();
                result.insert(*v);
                result
            }
            Node::And(items) => {
                let mut result = HashSet::new();
                for item in items {
                    result.extend(item.reference_variables())
                }
                result
            }
            Node::Or(items) => {
                let mut result = HashSet::new();
                for item in items {
                    result.extend(item.reference_variables())
                }
                result
            }
            Node::Not(x) => x.reference_variables(),
            Node::False | Node::True => HashSet::new(),
        }
    }

    /// return Some(true) if self node is subset of other,
    /// return Some(false) is self node is not subset of other.
    ///
    /// # subset
    ///
    /// when A is subset of B
    /// B contains all of A
    ///
    #[tracing::instrument]
    pub fn is_subset_of(&self, other: &Node) -> bool {
        let result = match (self, other) {
            // is_subset( A,A ) then Same set, not subset,
            // is_subset( A,B ) then other set, not subset
            (Node::Literal(_, _), Node::Literal(_, _)) => false,
            (Node::Literal(_, _), Node::And(_)) => false,
            (Node::Literal(_, _), Node::Or(or_items)) => {
                for item in or_items {
                    if item == self {
                        return true;
                    }
                }
                false
            }
            (Node::Literal(_, _), Node::Not(_)) => {
                false // TODO: verify
            }
            (Node::Literal(_, _), Node::False) => false,
            (Node::Literal(_, _), Node::True) => true,
            (Node::And(and_items), Node::Literal(_, _)) => {
                if and_items.contains(other) {
                    return true;
                }
                and_items.iter().any(|a| a.is_subset_of(other))
            }
            (Node::And(left), Node::And(right)) => !right.iter().any(|r| !left.contains(r)),
            (Node::And(and_items), Node::Or(or_items)) => {
                if and_items.iter().all(|a| or_items.contains(a)) {
                    return true;
                }
                // all and_items is subset of any or_items
                for and_item in and_items {
                    if !or_items.iter().any(|o| and_item.is_subset_of(o)) {
                        return false;
                    }
                }
                true
            }
            (Node::And(and_items), Node::Not(_)) => and_items.contains(other),
            (Node::And(_), Node::False) => false,
            (Node::And(_), Node::True) => true,
            (Node::Or(_), Node::Literal(_, _)) => false,
            (Node::Or(or_items), Node::And(_)) => or_items.iter().all(|o| o.is_subset_of(other)),
            (Node::Or(left), Node::Or(right)) => {
                for item in left {
                    if !right.iter().any(|o| item.is_subset_of(o)) {
                        return false;
                    }
                }
                true
            }
            (Node::Or(or_items), Node::Not(_)) => or_items.iter().all(|o| o.is_subset_of(other)),
            (Node::Or(_), Node::False) => false,
            (Node::Or(_), Node::True) => true,
            (Node::Not(_), Node::Literal(_, _)) => {
                false // TODO: verify
            }
            (Node::Not(_), Node::And(_)) => {
                false // TODO: verify
            }
            (Node::Not(_), Node::Or(or_items)) => or_items.iter().any(|item| item == self),
            (Node::Not(a), Node::Not(b)) => {
                //  if b is subset of a, outer a contains outer b
                b.is_subset_of(a)
            }
            (Node::Not(_), Node::False) => false,
            (Node::Not(_), Node::True) => true,
            (Node::False, _) => true, // false is subset of everything
            (Node::True, _) => false, // true is superset of everything
        };

        result
    }

    /// return Node when variable is value
    pub fn apply_context(&self, var: &Variable, value: bool) -> Node {
        match self {
            Node::Literal(v, lv) => {
                if v.index() == var.index() {
                    match (lv, value) {
                        (true, true) => Node::True,
                        (true, false) => Node::False,
                        (false, true) => Node::False,
                        (false, false) => Node::True,
                    }
                } else {
                    self.clone()
                }
            }
            Node::And(items) => {
                let mut items: Vec<Node> =
                    items.iter().map(|n| n.apply_context(var, value)).collect();
                items.retain(|n| !matches!(n, Node::True));
                Node::and_from_owned(items)
            }
            Node::Or(items) => {
                let items: Vec<Node> = items.iter().map(|n| n.apply_context(var, value)).collect();
                Node::or(items.iter().collect())
            }
            Node::Not(item) => Node::not(&item.apply_context(var, value)),
            Node::True | Node::False => self.clone(),
        }
    }

    /// enumerate context
    pub fn contexts(&self) -> HashSet<(Variable, bool)> {
        match self {
            Node::Literal(v, lv) => {
                let mut result = HashSet::new();
                result.insert((*v, *lv));
                result
            }
            Node::And(items) => {
                let mut result = HashSet::new();
                for item in items {
                    result.extend(item.contexts())
                }
                result
            }
            Node::Or(items) => {
                let mut result = HashSet::new();
                for item in items {
                    result.extend(item.contexts())
                }
                result
            }
            Node::Not(item) => {
                let inner = item.contexts();
                let mut result = HashSet::new();
                for item in inner {
                    result.insert((item.0, !item.1));
                }
                result
            }
            Node::True | Node::False => HashSet::new(),
        }
    }

    /// create and Node
    #[tracing::instrument]
    pub fn and(items: Vec<&Node>) -> Node {
        if items.len() == 1 {
            items[0].clone()
        } else {
            Node::And(items.into_iter().cloned().collect())
        }
    }

    /// create and Node from Owned Nodes
    #[tracing::instrument]
    pub fn and_from_owned(items: Vec<Node>) -> Node {
        if items.len() == 1 {
            items[0].to_owned()
        } else {
            Node::And(items)
        }
    }

    /// create or Node
    #[tracing::instrument]
    pub fn or(items: Vec<&Node>) -> Node {
        if items.len() == 1 {
            items[0].clone()
        } else {
            Node::Or(items.into_iter().cloned().collect())
        }
    }

    // Node is And or contains and
    #[tracing::instrument]
    fn have_and(&self) -> bool {
        match self {
            Node::Literal(_, _) => false,
            Node::And(_) => true,
            Node::Or(items) => items.iter().any(|n| n.have_and()),
            Node::Not(item) => item.deref().have_and(),
            Node::True | Node::False => false,
        }
    }

    #[tracing::instrument]
    fn two_or_to_and(switch_variable: Variable, left: Vec<Node>, right: Vec<Node>) -> Node {
        let lit = Self::lit(switch_variable);
        let not = Self::not(&lit);
        let mut result_item = Vec::new();
        for left_item in left {
            assert!(!left_item.have_and());
            result_item.push(Node::or(vec![&left_item, &lit]));
        }
        for right_item in right {
            assert!(!right_item.have_and());
            result_item.push(Node::or(vec![&right_item, &not]));
        }
        Node::and_from_owned(result_item)
    }

    /// convert node ot AND (OR( NOT( Literal )))
    #[tracing::instrument]
    pub fn to_and_or_not_form(&self, vars: &mut Variables) -> Self {
        fn create_and_from_or(vars: &mut Variables, or_node: Node) -> Node {
            if let Node::Or(items) = or_node {
                let mut and_nodes = Vec::new();
                let mut other_nodes = Vec::new();

                for item in items {
                    match item {
                        Node::And(_) => and_nodes.push(item),
                        _ => other_nodes.push(item),
                    }
                }

                if !other_nodes.is_empty() {
                    todo!()
                }

                //    (A && B && C)
                // || (D && E && F)
                // => (A||Z) && (B||Z) && (C||Z)
                // && (D||~Z) && (E||~Z) && (F||~Z)
                while and_nodes.len() >= 2 {
                    if let Some(Node::And(left_item)) = and_nodes.pop() {
                        if let Some(Node::And(right_item)) = and_nodes.pop() {
                            and_nodes.push(Node::two_or_to_and(
                                vars.create(),
                                left_item,
                                right_item,
                            ))
                        } else {
                            panic!("Not and!")
                        }
                    } else {
                        panic!("Not and!")
                    }
                }

                if and_nodes.is_empty() {
                    todo!()
                }

                and_nodes[0].clone()
            } else {
                panic!("Not or node!")
            }
        }

        let result = match self {
            Node::Literal(_, _) => self.clone(),
            Node::And(items) => {
                let new_items: Vec<Node> =
                    items.iter().map(|n| n.to_and_or_not_form(vars)).collect();
                let mut result_items = Vec::new();
                for item in new_items {
                    match item {
                        Node::And(mut items) => {
                            result_items.append(&mut items);
                        }
                        _ => result_items.push(item),
                    }
                }
                Node::and_from_owned(result_items)
            }
            Node::Or(items) => {
                let new_items: Vec<Node> =
                    items.iter().map(|n| n.to_and_or_not_form(vars)).collect();
                let result = if new_items.iter().all(|n| !n.have_and()) {
                    Node::or(new_items.iter().collect())
                } else {
                    let temp_or = Node::or(new_items.iter().collect());
                    match temp_or {
                        Node::Literal(_, _) => temp_or,
                        Node::And(_) => temp_or,
                        Node::Or(_) => create_and_from_or(vars, temp_or),
                        Node::Not(_) => temp_or,
                        Node::False => temp_or,
                        Node::True => temp_or,
                    }
                };
                if matches!(result, Node::Or(_)) {
                    if result.have_and() {
                        panic!("or have and!")
                    }
                }
                result
            }
            Node::Not(item) => match item.deref() {
                Node::Literal(_, _) => self.clone(),
                Node::And(_) => self.apply_de_morgan_law().to_and_or_not_form(vars),
                Node::Or(_) => self.apply_de_morgan_law().to_and_or_not_form(vars),
                Node::Not(x) => x.deref().to_and_or_not_form(vars),
                Node::False => self.clone(),
                Node::True => self.clone(),
            },
            Node::False => self.clone(),
            Node::True => self.clone(),
        };
        result
    }

    /// convert node to OR( AND( NOT( Literal ))) form a.k.a DNF
    ///
    /// # Algorithm
    ///
    /// 1. recursively apply "de morgan's law" to Not-And, Not-Or.
    ///   then, tree leaf is Literal or Not Literal
    /// 2. recursively apply cross-product to And node, output results Or-And
    /// 3. recursively apply flatten , marge And-And, marge Or-Or
    ///
    #[tracing::instrument]
    pub fn to_or_and_not_form(&self) -> Self {
        fn items_from_or(or_node: Node) -> Vec<Node> {
            match or_node {
                Node::Or(items) => items,
                _ => panic!("dont or node"),
            }
        }

        fn has_or(node: &Node) -> bool {
            match node {
                Node::Or(_) => true,
                Node::And(items) => {
                    for item in items {
                        if has_or(item) {
                            return true;
                        }
                    }
                    false
                }
                Node::Literal(_, _) => false,
                Node::Not(item) => has_or(item.deref()),
                Node::False => false,
                Node::True => false,
            }
        }

        fn constraind_create_and(items: Vec<&Node>) -> Node {
            for (index, item) in items.iter().enumerate() {
                if has_or(item) {
                    panic!("violate constrain {:} {:?}", index, item)
                }
            }
            Node::and(items)
        }

        fn cross_product_or_items(mut or_nodes: Vec<Node>) -> Vec<Node> {
            let mut or_items = Vec::new();
            if or_nodes.len() >= 2 {
                // (A || B) && (C || D) ...
                // (A&&C || A&&D || B&&C || B&&D)
                let first_set = items_from_or(or_nodes.pop().unwrap());
                let second_set = items_from_or(or_nodes.pop().unwrap());
                for right in first_set {
                    for left in &second_set {
                        or_items.push(constraind_create_and(vec![&right, left]))
                    }
                }
            } else {
                // only 1 or node in this And
                panic!("cross product on 1 node");
            }

            while let Some(Node::Or(childs)) = or_nodes.pop() {
                let head = or_items;
                or_items = Vec::new();
                for right in head {
                    for left in &childs {
                        or_items.push(constraind_create_and(vec![&right, left]))
                    }
                }
            }
            or_items
        }

        fn process_and_node(items: &[Node]) -> Node {
            let children: Vec<Node> = items
                .iter()
                .map(|child| child.to_or_and_not_form().flatten())
                .collect();

            // grouping children
            //
            // A && B && (C || D ) && E && (F || G)  =>
            //   (A && B && E)
            //    ~~~~~~~~~~~ and_node
            //   && ( C || D ) && ( F || G)
            //      ~~~~~~~~~~~~~~~~~~ or_nodes
            let mut or_nodes = Vec::new();
            let mut other_nodes = Vec::new();
            for item in children {
                match item {
                    Node::Literal(_, _)
                    | Node::And(_)
                    | Node::Not(_)
                    | Node::True
                    | Node::False => other_nodes.push(item),
                    Node::Or(_) => or_nodes.push(item.flatten()),
                }
            }
            if other_nodes.is_empty() {
                let result = Node::or(cross_product_or_items(or_nodes).iter().collect());
                return result;
            }

            let and_node = if other_nodes.len() == 1 {
                other_nodes.pop().unwrap()
            } else {
                constraind_create_and(other_nodes.iter().collect())
            };

            // if not contains or, and_node is result
            if or_nodes.is_empty() {
                return and_node;
            }
            // extract or_items
            let or_items = if or_nodes.len() == 1 {
                match or_nodes.pop().unwrap() {
                    Node::Or(items) => items,
                    _ => panic!("not or from or_nodes"),
                }
            } else {
                cross_product_or_items(or_nodes)
            };

            // cross product
            // (and_node) && (B || C) =>
            //    (and_node && B) || (and_node && C)
            let result = Node::Or(
                or_items
                    .iter()
                    .map(|i| constraind_create_and(vec![&and_node, i]))
                    .collect(),
            );

            result
        }

        let result = match self {
            Node::Literal(_, _) => self.to_owned(),
            Node::And(items) => process_and_node(items),
            Node::Or(items) => {
                let children: Vec<Node> = items
                    .iter()
                    .map(|child| child.to_or_and_not_form())
                    .collect();
                Node::or(children.iter().collect()).flatten()
            }
            Node::Not(item) => match item.deref() {
                Node::Literal(_, _) => self.clone(),
                Node::Or(_) => self.apply_de_morgan_law().to_or_and_not_form(),
                Node::And(_) => self.apply_de_morgan_law().to_or_and_not_form(),
                Node::Not(not2) => not2.to_or_and_not_form(),
                Node::False => self.clone(),
                Node::True => self.clone(),
            },
            Node::False => self.clone(),
            Node::True => self.clone(),
        };
        result
    }

    /// returns flatten represent for Node
    ///
    /// - marge nested Or (Or)
    /// - marge nested And (And)
    /// - convert Not(Not(x)) into x
    ///
    #[tracing::instrument]
    pub fn flatten(&self) -> Self {
        let result = match self {
            Node::Literal(_, _) | Node::False | Node::True => self.clone(),
            Node::Or(items) => {
                let mut child_items: Vec<Node> = (*items).iter().map(|n| n.flatten()).collect();
                // A || ( (B&&C) || D )
                // =>  A || (B && C) || D
                let mut or_items = Vec::new();
                while let Some(child) = child_items.pop() {
                    match child {
                        Node::Or(mut or_content) => child_items.append(&mut or_content),
                        Node::Not(_) | Node::Literal(_, _) | Node::And(_) | Node::False => {
                            or_items.push(child)
                        }
                        Node::True => return Node::True,
                    }
                }
                Node::or(or_items.iter().collect())
            }
            Node::And(items) => {
                let mut child_items: Vec<Node> = (*items).iter().map(|n| n.flatten()).collect();
                let mut and_items = Vec::new();
                while let Some(child) = child_items.pop() {
                    match child {
                        Node::And(mut and_content) => child_items.append(&mut and_content),
                        Node::Not(_) | Node::Literal(_, _) | Node::Or(_) | Node::True => {
                            and_items.push(child.clone())
                        }
                        Node::False => return Node::False,
                    }
                }
                Node::and_from_owned(and_items)
            }
            Node::Not(child) => match child.deref() {
                Node::Literal(_, _) | Node::And(_) | Node::Or(_) => self.clone(),
                Node::Not(item) => item.deref().clone(),
                Node::False => Node::True,
                Node::True => Node::False,
            },
        };
        result
    }

    #[tracing::instrument]
    fn apply_de_morgan_law(&self) -> Self {
        fn wrap_child(items: &[Node]) -> Vec<Node> {
            (*items).iter().map(|f| Node::not(f)).collect()
        }

        match self {
            Node::Literal(_, _) => self.clone(),
            Node::Or(items) => {
                let and_items = wrap_child(items);
                Node::not(&Node::and_from_owned(and_items))
            }
            Node::And(items) => Node::not(&Node::or(wrap_child(items).iter().collect())),
            Node::Not(child) => match child.deref() {
                Node::Literal(_, _) => self.clone(),
                Node::And(items) => Node::Or(wrap_child(items)),
                Node::Or(items) => {
                    let and_items = wrap_child(items);
                    Node::and_from_owned(and_items)
                }
                Node::Not(_) => self.clone(),
                Node::False => self.clone(),
                Node::True => self.clone(),
            },
            Node::False => self.clone(),
            Node::True => self.clone(),
        }
    }

    /// create literal
    #[tracing::instrument]
    pub fn lit(variable: Variable) -> Self {
        Node::Literal(variable, true)
    }

    /// create not
    #[tracing::instrument]
    pub fn not(item: &Node) -> Self {
        match item {
            Node::Literal(v, d) => Node::Literal(*v, !d),
            Node::True => Node::False,
            Node::False => Node::True,
            Node::Not(base) => base.deref().clone(),
            _ => Node::Not(Box::new(item.to_owned())),
        }
    }

    /// builds 2 input xor
    ///
    /// returns (left and ~right) or (~left and right)
    #[tracing::instrument]
    pub fn xor2(left: &Node, right: &Node) -> Node {
        Self::or(vec![
            &Self::and(vec![left, &Self::not(right)]),
            &Self::and(vec![&Self::not(left), right]),
        ])
    }

    /// one_of( A,B,C )
    ///
    /// builds
    ///
    /// ```text
    ///  ( ( A && ~B && ~C)
    /// || (~A &&  B && ~C)
    /// || (~A && ~B &&  C) )
    /// ```
    #[tracing::instrument]
    pub fn one_of(nodes: Vec<Node>) -> Node {
        if nodes.len() == 1 {
            return nodes[0].clone();
        }
        let length = nodes.len();
        let mut or_set = Vec::new();
        for index in 0..length {
            let mut childs = Vec::new();
            for (i, item) in nodes.iter().enumerate().take(length) {
                childs.push(if i == index {
                    item.clone()
                } else {
                    Self::not(item)
                })
            }
            or_set.push(Node::and_from_owned(childs))
        }
        Node::Or(or_set)
    }
}

/// create literal node
///
/// short-cut for Node::lit
///
pub fn lit(variable: Variable) -> Node {
    Node::lit(variable)
}

/// create and node
///
/// short-cut for Node::and
///
pub fn and(mut items: Vec<&Node>) -> Node {
    items.sort();
    items.dedup();
    Node::and(items)
}

/// create binary and node
///
/// short-cut for Node::and
///
pub fn and2(left: &Node, right: &Node) -> Node {
    and(vec![left, right])
}

/// create ternary and node
///
/// short-cut for Node::and
///
pub fn and3(left: &Node, mid: &Node, right: &Node) -> Node {
    and(vec![left, mid, right])
}

/// create or node
///
/// short-cut for Node::or
///
pub fn or(mut items: Vec<&Node>) -> Node {
    items.sort();
    items.dedup();
    Node::or(items)
}

/// create binary or node
///
/// short-cut for Node::or
///
pub fn or2(left: &Node, right: &Node) -> Node {
    or(vec![left, right])
}

/// create ternary or node
///
/// short-cut for Node::or
///
pub fn or3(left: &Node, mid: &Node, right: &Node) -> Node {
    or(vec![left, mid, right])
}

/// create not node
///
/// short-cut for Node::not
pub fn not(item: &Node) -> Node {
    Node::not(item)
}

/// short-cut for Node::one_of
pub fn one_of(nodes: Vec<Node>) -> Node {
    Node::one_of(nodes)
}

/// short-cut for Node::xor2
pub fn xor2(left: &Node, right: &Node) -> Node {
    Node::xor2(left, right)
}

/// TreeBuilder helps build Node

#[cfg(test)]
mod tests {
    use test_case::test_case;

    use crate::{
        boolean_expression::{and3, or3},
        not,
        solver::Variables,
    };

    use super::{and, and2, lit, or, or2, Node};

    struct Literals {
        pub lit1: Node,
        pub lit2: Node,
        pub lit3: Node,
    }

    impl Literals {
        pub fn new() -> Literals {
            let mut vars = Variables::new();
            Literals {
                lit1: lit(vars.create()),
                lit2: lit(vars.create()),
                lit3: lit(vars.create()),
            }
        }

        pub fn lit1(&self) -> Node {
            self.lit1.clone()
        }
        pub fn lit2(&self) -> Node {
            self.lit2.clone()
        }
        pub fn lit3(&self) -> Node {
            self.lit3.clone()
        }
    }

    #[test_case( Literals::new(), |lits| {lits.lit1()} => Some(1) ; "lit1 reference varable#1" )]
    #[test_case( Literals::new(), |lits| {lits.lit2()} => Some(2) ; "lit2 reference varable#2" )]
    #[test_case( Literals::new(), |lits| {lits.lit3()} => Some(3) ; "lit3 reference varable#3" )]
    fn test_literals(lits: Literals, f: fn(&Literals) -> Node) -> Option<u32> {
        let node = f(&lits);
        node.index()
    }

    #[test]
    fn test_tree_builder_lit() {
        let mut vars = Variables::new();
        let node = lit(vars.create());
        match node {
            Node::Literal(v, _) => {
                assert_eq!(v.index(), 1)
            }
            _ => panic!("BAD NODE {:?}", node),
        }
    }

    #[test]
    fn test_tree_builder_lit_and() {
        let mut vars = Variables::new();
        let node1 = lit(vars.create());
        let node2 = lit(vars.create());
        let and_node = and2(&node1, &node2);
        match and_node {
            Node::And(items) => {
                assert_eq!((*items).len(), 2)
            }
            _ => panic!("BAD NODE {:?}", and_node),
        }
    }

    #[test]
    fn test_tree_builder_lit_or() {
        let mut vars = Variables::new();
        let node1 = lit(vars.create());
        let node2 = lit(vars.create());
        let or_node = or2(&node1, &node2);
        match or_node {
            Node::Or(items) => {
                assert_eq!((*items).len(), 2)
            }
            _ => panic!("BAD NODE {:?}", or_node),
        }
    }

    #[test]
    fn test_tree_builder_lit_not() {
        let mut vars = Variables::new();
        let node1 = lit(vars.create());
        let not_node = not(&node1);
        match not_node {
            Node::Literal(l, d) => {
                assert_eq!(l.index(), 1);
                assert_eq!(d, false);
            }
            _ => panic!("BAD NODE {:?}", not_node),
        }
        let not2_node = not(&not_node);
        match not2_node {
            Node::Literal(l, d) => {
                assert_eq!(l.index(), 1);
                assert_eq!(d, true)
            }
            _ => panic!("BAD NODE {:?}", not2_node),
        }
    }

    #[test]
    fn test_flatten_or() {
        let mut vars = Variables::new();
        let lit1 = lit(vars.create());
        let lit2 = lit(vars.create());
        let nested_or = or3(&or2(&lit1, &lit1), &lit2, &lit1);
        let exp = format!("{}", nested_or);
        assert_eq!(exp, "([1]||[2])");
        let nested_or = nested_or.flatten(); // flatten to be deprecated
        let exp = format!("{}", nested_or);
        assert_eq!(exp, "([2]||[1])");
    }

    #[test]
    fn test_flatten_and() {
        let mut vars = Variables::new();
        let lit1 = lit(vars.create());
        let lit2 = lit(vars.create());
        let nested_and = and3(&and2(&lit1, &lit1), &lit2, &lit1);
        let exp = format!("{}", nested_and);
        assert_eq!(exp, "([1]&&[2])");
        let nested_and = nested_and.flatten(); // flatten to be deprecated
        let exp = format!("{}", nested_and);
        assert_eq!(exp, "([2]&&[1])");
    }

    #[test]
    fn test_apply_de_morgan_law() {
        let mut vars = Variables::new();
        let lit1 = lit(vars.create());
        let lit2 = lit(vars.create());
        let lit3 = lit(vars.create());
        let result = and(vec![&lit1]).apply_de_morgan_law().flatten();
        assert_eq!(format!("{}", result), "[1]");
        let result = and2(&lit1, &lit2).apply_de_morgan_law().flatten();
        assert_eq!(format!("{}", result), "!(([~1]||[~2]))");
        let result = and3(&lit1, &lit2, &lit3).apply_de_morgan_law().flatten();
        assert_eq!(format!("{}", result), "!(([~1]||[~2]||[~3]))");

        let result = not(&and(vec![&lit1])).apply_de_morgan_law().flatten();
        assert_eq!(format!("{}", result), "[~1]");
        let result = not(&and2(&lit1, &lit2)).apply_de_morgan_law().flatten();
        assert_eq!(format!("{}", result), "([~2]||[~1])");
        let result = not(&and3(&lit1, &lit2, &lit3))
            .apply_de_morgan_law()
            .flatten();
        assert_eq!(format!("{}", result), "([~3]||[~2]||[~1])");

        let result = or(vec![&lit1]).apply_de_morgan_law().flatten();
        assert_eq!(format!("{}", result), "[1]");
        let result = or2(&lit1, &lit2).apply_de_morgan_law().flatten();
        assert_eq!(format!("{}", result), "!(([~1]&&[~2]))");
        let result = or3(&lit1, &lit2, &lit3).apply_de_morgan_law().flatten();
        assert_eq!(format!("{}", result), "!(([~1]&&[~2]&&[~3]))");

        let result = not(&or(vec![&lit1])).apply_de_morgan_law().flatten();
        assert_eq!(format!("{}", result), "[~1]");
        let result = not(&or2(&lit1, &lit2)).apply_de_morgan_law().flatten();
        assert_eq!(format!("{}", result), "([~2]&&[~1])");
        let result = not(&or3(&lit1, &lit2, &lit3))
            .apply_de_morgan_law()
            .flatten();
        assert_eq!(format!("{}", result), "([~3]&&[~2]&&[~1])");

        let result = and2(&lit1, &not(&lit2)).apply_de_morgan_law().flatten();
        assert_eq!(format!("{}", result), "!(([~1]||[2]))");
        let result = or2(&lit1, &not(&lit2)).apply_de_morgan_law().flatten();
        assert_eq!(format!("{}", result), "!(([~1]&&[2]))");
    }

    #[test]
    fn test_build_cnf() {
        let mut vars = Variables::new();
        let lit1 = lit(vars.create());
        let lit2 = lit(vars.create());
        let lit3 = lit(vars.create());
        let lit4 = lit(vars.create());
        let lit5 = lit(vars.create());

        let result = and2(&or2(&lit1, &lit2), &lit3)
            .to_or_and_not_form()
            .flatten();
        assert_eq!(format!("{}", result), "(([1]&&[3])||([2]&&[3]))");
        let result = and2(&or2(&lit1, &lit2), &or2(&lit3, &lit4))
            .to_or_and_not_form()
            .flatten();
        assert_eq!(
            format!("{}", result),
            "(([1]&&[3])||([2]&&[3])||([1]&&[4])||([2]&&[4]))"
        );
        let result = and2(&or2(&lit1, &lit2), &or3(&lit3, &lit4, &lit5))
            .to_or_and_not_form()
            .flatten();
        assert_eq!(
            format!("{}", result),
            "(([1]&&[3])||([2]&&[3])||([1]&&[4])||([2]&&[4])||([1]&&[5])||([2]&&[5]))"
        );

        let result = and2(&not(&or2(&lit1, &lit2)), &or3(&lit3, &lit4, &lit5))
            .to_or_and_not_form()
            .flatten();
        assert_eq!(
            format!("{}", result),
            "(([3]&&[~2]&&[~1])||([4]&&[~2]&&[~1])||([5]&&[~2]&&[~1]))"
        );
    }

    #[test]
    fn test_subset_of() {
        let mut vars = Variables::new();
        let lit1 = lit(vars.create());
        let lit2 = lit(vars.create());
        let lit3 = lit(vars.create());

        let and2 = and2(&lit1, &lit2);
        let and3 = and3(&lit1, &lit2, &lit3);

        assert_eq!(lit1.is_subset_of(&and2), false);
        assert_eq!(and2.is_subset_of(&lit1), true);
        assert_eq!(and3.is_subset_of(&and2), true);
        assert_eq!(and2.is_subset_of(&and3), false);

        let or2 = or2(&lit1, &lit2);
        assert_eq!(lit1.is_subset_of(&or2), true);
        assert_eq!(lit2.is_subset_of(&or2), true);
        assert_eq!(lit3.is_subset_of(&or2), false);
        assert_eq!(and2.is_subset_of(&or2), true);
    }

    #[test_case( Literals::new(), |lits| {and2(&lits.lit1, &lits.lit2)}, |lits| {lits.lit1()} => true; "A and B is subset of A")]
    #[test_case( Literals::new(), |lits| {lits.lit1()}, |lits| {and2(&lits.lit1, &lits.lit2)} => false; "A is not subset of A and B")]
    #[test_case( Literals::new(), |lits| {or2(&lits.lit1, &lits.lit2)}, |lits| {lits.lit1()} => false; "A or B is not subset of A")]
    #[test_case( Literals::new(), |lits| {lits.lit1()}, |lits| {or2(&lits.lit1, &lits.lit2)} => true; "A is subset of A or B")]
    fn test_is_subset_of(
        lits: Literals,
        this: fn(&Literals) -> Node,
        other: fn(&Literals) -> Node,
    ) -> bool {
        let this_node = this(&lits);
        let other_node = other(&lits);
        this_node.is_subset_of(&other_node)
    }

    #[test]
    fn test_subset_false_is_subset_of_everything() {
        let mut vars = Variables::new();
        let lit1 = lit(vars.create());
        let lit2 = lit(vars.create());

        let and2 = and2(&lit1, &lit2);
        let or2 = or2(&lit1, &lit2);
        let not_lit = not(&lit1);

        assert_eq!(lit1.is_subset_of(&Node::False), false);
        assert_eq!(and2.is_subset_of(&Node::False), false);
        assert_eq!(or2.is_subset_of(&Node::False), false);
        assert_eq!(not_lit.is_subset_of(&Node::False), false);
        assert_eq!(Node::True.is_subset_of(&Node::False), false);

        assert_eq!(Node::False.is_subset_of(&lit1), true);
        assert_eq!(Node::False.is_subset_of(&and2), true);
        assert_eq!(Node::False.is_subset_of(&or2), true);
        assert_eq!(Node::False.is_subset_of(&not_lit), true);
        assert_eq!(Node::False.is_subset_of(&Node::False), true);
        assert_eq!(Node::False.is_subset_of(&Node::True), true);

        // special rule for Node::False,
        // other Node variants, never both true:
        //  A.is_subset_of(B) and B.is_subset_of(A)
        assert_eq!(Node::False.is_subset_of(&Node::False), true);
    }

    #[test]
    fn test_subset_true_is_superset_of_everything() {
        let mut vars = Variables::new();
        let lit1 = lit(vars.create());
        let lit2 = lit(vars.create());

        let and2 = and2(&lit1, &lit2);
        let or2 = or2(&lit1, &lit2);
        let not_lit = not(&lit1);

        assert_eq!(lit1.is_subset_of(&Node::True), true);
        assert_eq!(and2.is_subset_of(&Node::True), true);
        assert_eq!(or2.is_subset_of(&Node::True), true);
        assert_eq!(not_lit.is_subset_of(&Node::True), true);
        assert_eq!(Node::False.is_subset_of(&Node::True), true);

        assert_eq!(Node::True.is_subset_of(&lit1), false);
        assert_eq!(Node::True.is_subset_of(&and2), false);
        assert_eq!(Node::True.is_subset_of(&or2), false);
        assert_eq!(Node::True.is_subset_of(&not_lit), false);
        assert_eq!(Node::True.is_subset_of(&Node::False), false);

        assert_eq!(Node::True.is_subset_of(&Node::True), false);
    }

    #[test]
    fn test_apply_context() {
        let mut vars = Variables::new();
        let lit1 = lit(vars.create());
        let var2 = vars.create();
        let lit2 = lit(var2);
        let lit3 = lit(vars.create());

        let node = and3(&lit3, &not(&lit1), &not(&lit2));
        let result = node.apply_context(&var2, false);
        assert_eq!(format!("{}", result), "([~1]&&[3])");
    }
}
