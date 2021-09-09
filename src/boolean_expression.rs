use std::{cmp::Ordering, fmt::Display, ops::Deref};

use crate::solver::{Variable, Variables};

/// boolean expression node
#[derive(Debug, PartialEq, Clone, Eq)]
pub enum Node {
    /// Literal, references SAT variable
    Literal(Variable),
    /// And, true if all Node is true
    And(Vec<Node>),
    /// Or, true if any Node is true
    Or(Vec<Node>),
    /// Node, true if Node is false
    Not(Box<Node>),
}

impl Ord for Node {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl PartialOrd for Node {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Node::Literal(v1), Node::Literal(v2)) => v1.index().partial_cmp(&v2.index()),
            (Node::And(items1), Node::And(items2)) => {
                let items1 = items1.deref();
                let items2 = items2.deref();
                let comp_len = items1.len().min(items2.len());
                for index in 0..comp_len {
                    match items1[index].partial_cmp(&items2[index]) {
                        Some(Ordering::Equal) => continue,
                        Some(Ordering::Greater) => return Some(Ordering::Less),
                        Some(Ordering::Less) => return Some(Ordering::Greater),
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
                        Some(Ordering::Greater) => return Some(Ordering::Less),
                        Some(Ordering::Less) => return Some(Ordering::Greater),
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
            (Node::Literal(_), Node::And(_)) => Some(Ordering::Less),
            (Node::Literal(_), Node::Or(_)) => Some(Ordering::Less),
            (Node::Literal(_), Node::Not(_)) => Some(Ordering::Less),
            (Node::And(_), Node::Literal(_)) => Some(Ordering::Greater),
            (Node::And(_), Node::Or(_)) => Some(Ordering::Less),
            (Node::And(_), Node::Not(_)) => Some(Ordering::Greater),
            (Node::Or(_), Node::Literal(_)) => Some(Ordering::Less),
            (Node::Or(_), Node::And(_)) => Some(Ordering::Less),
            (Node::Or(_), Node::Not(_)) => Some(Ordering::Greater),
            (Node::Not(_), Node::Literal(_)) => Some(Ordering::Less),
            (Node::Not(_), Node::And(_)) => Some(Ordering::Less),
            (Node::Not(_), Node::Or(_)) => Some(Ordering::Less),
        }
    }
}

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            Node::Literal(v) => {
                write!(f, "[{}]", v.index())?;
            }
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
        }
        Ok(())
    }
}

impl Node {
    /// convert node to OR( AND( NOT( Literal ))) form
    ///
    /// # Algorithm
    ///
    /// 1. recursively apply "de morgan's law" to Not-And, Not-Or.
    ///   then, tree leaf is Literal or Not Literal
    /// 2. recursively apply cross-product to And node, output results Or-And
    /// 3. recursively apply flatten , marge And-And, marge Or-Or
    ///
    pub fn to_or_and_not_form(&self) -> Self {
        fn items_from_or(or_node: Node) -> Vec<Node> {
            match or_node {
                Node::Or(items) => items,
                _ => panic!("dont or node"),
            }
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
                        or_items.push(Node::And(vec![right.clone(), left.clone()]))
                    }
                }
            } else {
                // only 1 or node in this And
                return or_nodes;
            }

            while let Some(Node::Or(childs)) = or_nodes.pop() {
                let head = or_items;
                or_items = Vec::new();
                for right in head {
                    for left in &childs {
                        or_items.push(Node::And(vec![right.clone(), left.clone()]))
                    }
                }
            }
            or_items
        }

        match self {
            Node::Literal(_) => self.to_owned(),
            Node::And(items) => {
                let children: Vec<Node> = items
                    .iter()
                    .map(|child| child.to_or_and_not_form())
                    .collect();

                // grouping children
                //
                // A && B && (C || D ) && E && (F || G)  =>
                //   (A && B && E)
                //    ~~~~~~~~~~~ and_node
                //   && ( C || D ) && ( F|| G)
                //      ~~~~~~~~~~~~~~~~~~~~~~ or_nodes
                let mut or_nodes = Vec::new();
                let mut other_nodes = Vec::new();
                for item in children {
                    match item {
                        Node::Literal(_) | Node::And(_) | Node::Not(_) => other_nodes.push(item),
                        Node::Or(_) => or_nodes.push(item),
                    }
                }
                if other_nodes.is_empty() {
                    return Node::Or(cross_product_or_items(or_nodes));
                }
                let and_node = Node::And(other_nodes);

                // if not contains or, and_node is result
                if or_nodes.is_empty() {
                    return and_node;
                }
                // extract or_items
                let or_items = cross_product_or_items(or_nodes);
                // cross product
                // (and_node) && (B || C) =>
                //    (and_node && B) || (and_node && C)
                Node::Or(
                    or_items
                        .iter()
                        .map(|i| Node::And(vec![and_node.clone(), i.clone()]))
                        .collect(),
                )
            }
            Node::Or(items) => {
                let children: Vec<Node> = items
                    .iter()
                    .map(|child| child.to_or_and_not_form())
                    .collect();
                Node::Or(children)
            }
            Node::Not(item) => match item.deref() {
                Node::Literal(_) => self.clone(),
                Node::Or(_) => self.apply_de_morgan_law().to_or_and_not_form(),
                Node::And(_) => self.apply_de_morgan_law().to_or_and_not_form(),
                Node::Not(not2) => not2.to_or_and_not_form(),
            },
        }
    }

    /// returns flatten represent for Node
    ///
    /// - marge nested Or (Or)
    /// - marge nested And (And)
    /// - convert Not(Not(x)) into x
    ///
    pub fn flatten(&self) -> Self {
        let result = match self {
            Node::Literal(_) => self.clone(),
            Node::Or(items) => {
                let child_items: Vec<Node> = (*items).iter().map(|n| n.flatten()).collect();
                // A || ( (B&&C) || D )
                // =>  A || (B && C) || D
                let mut or_items = Vec::new();
                for child in child_items {
                    match child {
                        Node::Literal(_) => or_items.push(child),
                        Node::And(_) => or_items.push(child),
                        Node::Or(mut or_content) => or_items.append(&mut or_content),
                        Node::Not(_) => or_items.push(child),
                    }
                }
                Node::Or(or_items)
            }
            Node::And(items) => {
                let child_items: Vec<Node> = (*items).iter().map(|n| n.flatten()).collect();
                let mut and_items = Vec::new();
                for child in child_items {
                    match child {
                        Node::Literal(_) => and_items.push(child),
                        Node::And(mut and_content) => and_items.append(&mut and_content),
                        Node::Or(_) => and_items.push(child),
                        Node::Not(_) => and_items.push(child),
                    }
                }
                Node::And(and_items)
            }
            Node::Not(child) => match child.deref() {
                Node::Literal(_) | Node::And(_) | Node::Or(_) => self.clone(),
                Node::Not(item) => item.deref().clone(),
            },
        };
        result.compact()
    }

    fn apply_de_morgan_law(&self) -> Self {
        fn wrap_not(child: &Node) -> Node {
            if let Node::Not(inner) = child {
                inner.deref().to_owned()
            } else {
                Node::Not(Box::new(child.to_owned()))
            }
        }

        fn wrap_child(items: &[Node]) -> Vec<Node> {
            (*items).iter().map(|f| wrap_not(f)).collect()
        }

        match self {
            Node::Literal(_) => self.clone(),
            Node::Or(items) => Node::Not(Box::new(Node::And(wrap_child(items)))),
            Node::And(items) => Node::Not(Box::new(Node::Or(wrap_child(items)))),
            Node::Not(child) => match child.deref() {
                Node::Literal(_) => self.clone(),
                Node::And(items) => Node::Or(wrap_child(items)),
                Node::Or(items) => Node::And(wrap_child(items)),
                Node::Not(_) => self.clone(),
            },
        }
    }

    fn compact(&self) -> Self {
        match self {
            Node::Literal(_) => self.clone(),
            Node::Not(_) => self.clone(),
            Node::Or(items) => {
                let mut items = (*items).clone();
                items.sort();
                // A || A || A => A
                items.dedup();
                Node::Or(items)
            }
            Node::And(items) => {
                let mut items = (*items).clone();
                items.sort();
                // A && A && A => A
                items.dedup();
                Node::And(items)
            }
        }
    }
}

/// TreeBuilder helps build Node
pub struct TreeBuilder {
    vars: Variables,
}

impl TreeBuilder {
    /// create instance TreeBuilder
    pub fn new(vars: Variables) -> Self {
        Self { vars }
    }

    /// build literal node
    pub fn lit(&mut self) -> Node {
        Node::Literal(self.vars.create())
    }

    /// build and node
    pub fn and(&self, items: Vec<Node>) -> Node {
        Node::And(items)
    }

    /// build 2 input and
    pub fn and2(&self, left: Node, right: Node) -> Node {
        Node::And(vec![left, right])
    }

    /// build 3 input and
    pub fn and3(&self, left: Node, mid: Node, right: Node) -> Node {
        Node::And(vec![left, mid, right])
    }

    /// build or node
    pub fn or(&self, items: Vec<Node>) -> Node {
        Node::Or(items)
    }

    /// build 2 input or
    pub fn or2(&self, left: Node, right: Node) -> Node {
        Node::Or(vec![left, right])
    }

    /// build 3 input or
    pub fn or3(&self, left: Node, mid: Node, right: Node) -> Node {
        Node::Or(vec![left, mid, right])
    }

    /// build not
    pub fn not(&self, item: Node) -> Node {
        match item {
            Node::Not(base) => base.deref().clone(),
            _ => Node::Not(Box::new(item.to_owned())),
        }
    }

    /// builds 2 input xor
    ///
    /// returns (left and ~right) or (~left and right)
    pub fn xor2(&self, left: Node, right: Node) -> Node {
        self.or2(
            self.and2(left.clone(), self.not(right.clone())),
            self.and2(self.not(left), right),
        )
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
    pub fn one_of(&mut self, nodes: Vec<Node>) -> Node {
        let length = nodes.len();
        let mut or_set = Vec::new();
        for index in 0..length {
            let mut childs = Vec::new();
            for (i, item) in nodes.iter().enumerate().take(length) {
                childs.push(if i == index {
                    item.clone()
                } else {
                    self.not(item.clone())
                })
            }
            or_set.push(Node::And(childs))
        }
        Node::Or(or_set)
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Deref;

    use crate::solver::Variables;

    use super::{Node, TreeBuilder};

    #[test]
    fn test_tree_builder_lit() {
        let mut b = TreeBuilder::new(Variables::new());
        let node = b.lit();
        match node {
            Node::Literal(v) => {
                assert_eq!(v.index(), 1)
            }
            _ => panic!("BAD NODE {:?}", node),
        }
    }

    #[test]
    fn test_tree_builder_lit_and() {
        let mut b = TreeBuilder::new(Variables::new());
        let node1 = b.lit();
        let node2 = b.lit();
        let and_node = b.and2(node1, node2);
        match and_node {
            Node::And(items) => {
                assert_eq!((*items).len(), 2)
            }
            _ => panic!("BAD NODE {:?}", and_node),
        }
    }

    #[test]
    fn test_tree_builder_lit_or() {
        let mut b = TreeBuilder::new(Variables::new());
        let node1 = b.lit();
        let node2 = b.lit();
        let or_node = b.or2(node1, node2);
        match or_node {
            Node::Or(items) => {
                assert_eq!((*items).len(), 2)
            }
            _ => panic!("BAD NODE {:?}", or_node),
        }
    }

    #[test]
    fn test_tree_builder_lit_not() {
        let mut b = TreeBuilder::new(Variables::new());
        let node1 = b.lit();
        let not_node = b.not(node1);
        match not_node {
            Node::Not(ref item) => match item.deref() {
                Node::Literal(l) => assert_eq!(l.index(), 1),
                _ => panic!("BAD Literal {:?}", item),
            },
            _ => panic!("BAD NODE {:?}", not_node),
        }
        let not2_node = b.not(not_node);
        match not2_node {
            Node::Literal(l) => assert_eq!(l.index(), 1),
            _ => panic!("BAD NODE {:?}", not2_node),
        }
    }

    #[test]
    fn test_flatten_or() {
        let mut b = TreeBuilder::new(Variables::new());
        let lit1 = b.lit();
        let lit2 = b.lit();
        let nested_or = b.or3(b.or(vec![lit1.clone()]), lit2, lit1);
        let nested_or = nested_or.flatten();
        let exp = format!("{}", nested_or);
        assert_eq!(exp, "([1]||[2])");
    }

    #[test]
    fn test_flatten_and() {
        let mut b = TreeBuilder::new(Variables::new());
        let lit1 = b.lit();
        let lit2 = b.lit();
        let nested_and = b.and3(b.and(vec![lit1.clone()]), lit2, lit1);
        let nested_and = nested_and.flatten();
        let exp = format!("{}", nested_and);
        assert_eq!(exp, "([1]&&[2])");
    }

    #[test]
    fn test_apply_de_morgan_law() {
        let mut b = TreeBuilder::new(Variables::new());
        let lit1 = b.lit();
        let lit2 = b.lit();
        let lit3 = b.lit();
        let result = b.and(vec![lit1.clone()]).apply_de_morgan_law().flatten();
        assert_eq!(format!("{}", result), "!((!([1])))");
        let result = b
            .and2(lit1.clone(), lit2.clone())
            .apply_de_morgan_law()
            .flatten();
        assert_eq!(format!("{}", result), "!((!([1])||!([2])))");
        let result = b
            .and3(lit1.clone(), lit2.clone(), lit3.clone())
            .apply_de_morgan_law()
            .flatten();
        assert_eq!(format!("{}", result), "!((!([1])||!([2])||!([3])))");

        let result = b
            .not(b.and(vec![lit1.clone()]))
            .apply_de_morgan_law()
            .flatten();
        assert_eq!(format!("{}", result), "(!([1]))");
        let result = b
            .not(b.and2(lit1.clone(), lit2.clone()))
            .apply_de_morgan_law()
            .flatten();
        assert_eq!(format!("{}", result), "(!([1])||!([2]))");
        let result = b
            .not(b.and3(lit1.clone(), lit2.clone(), lit3.clone()))
            .apply_de_morgan_law()
            .flatten();
        assert_eq!(format!("{}", result), "(!([1])||!([2])||!([3]))");

        let result = b.or(vec![lit1.clone()]).apply_de_morgan_law().flatten();
        assert_eq!(format!("{}", result), "!((!([1])))");
        let result = b
            .or2(lit1.clone(), lit2.clone())
            .apply_de_morgan_law()
            .flatten();
        assert_eq!(format!("{}", result), "!((!([1])&&!([2])))");
        let result = b
            .or3(lit1.clone(), lit2.clone(), lit3.clone())
            .apply_de_morgan_law()
            .flatten();
        assert_eq!(format!("{}", result), "!((!([1])&&!([2])&&!([3])))");

        let result = b
            .not(b.or(vec![lit1.clone()]))
            .apply_de_morgan_law()
            .flatten();
        assert_eq!(format!("{}", result), "(!([1]))");
        let result = b
            .not(b.or2(lit1.clone(), lit2.clone()))
            .apply_de_morgan_law()
            .flatten();
        assert_eq!(format!("{}", result), "(!([1])&&!([2]))");
        let result = b
            .not(b.or3(lit1.clone(), lit2.clone(), lit3.clone()))
            .apply_de_morgan_law()
            .flatten();
        assert_eq!(format!("{}", result), "(!([1])&&!([2])&&!([3]))");

        let result = b
            .and2(lit1.clone(), b.not(lit2.clone()))
            .apply_de_morgan_law()
            .flatten();
        assert_eq!(format!("{}", result), "!((!([1])||[2]))");
        let result = b
            .or2(lit1.clone(), b.not(lit2.clone()))
            .apply_de_morgan_law()
            .flatten();
        assert_eq!(format!("{}", result), "!((!([1])&&[2]))");
    }

    #[test]
    fn test_build_cnf() {
        let mut b = TreeBuilder::new(Variables::new());
        let lit1 = b.lit();
        let lit2 = b.lit();
        let lit3 = b.lit();
        let lit4 = b.lit();
        let lit5 = b.lit();

        let result = b
            .and2(b.or2(lit1.clone(), lit2.clone()), lit3.clone())
            .to_or_and_not_form()
            .flatten();
        assert_eq!(format!("{}", result), "(([2]&&[3])||([1]&&[3]))");
        let result = b
            .and2(
                b.or2(lit1.clone(), lit2.clone()),
                b.or2(lit3.clone(), lit4.clone()),
            )
            .to_or_and_not_form()
            .flatten();
        assert_eq!(
            format!("{}", result),
            "(([2]&&[4])||([2]&&[3])||([1]&&[4])||([1]&&[3]))"
        );
        let result = b
            .and2(
                b.or2(lit1.clone(), lit2.clone()),
                b.or3(lit3.clone(), lit4.clone(), lit5.clone()),
            )
            .to_or_and_not_form()
            .flatten();
        assert_eq!(
            format!("{}", result),
            "(([2]&&[5])||([2]&&[4])||([2]&&[3])||([1]&&[5])||([1]&&[4])||([1]&&[3]))"
        );

        let result = b
            .and2(
                b.not(b.or2(lit1.clone(), lit2.clone())),
                b.or3(lit3.clone(), lit4.clone(), lit5.clone()),
            )
            .to_or_and_not_form()
            .flatten();
        assert_eq!(
            format!("{}", result),
            "(([5]&&!([1])&&!([2]))||([4]&&!([1])&&!([2]))||([3]&&!([1])&&!([2])))"
        );
    }
}
