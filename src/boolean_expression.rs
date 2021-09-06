use std::{cmp::Ordering, fmt::Display, ops::Deref};

use crate::solver::{Variable, Variables};

#[derive(Debug, PartialEq, Clone, Eq)]
pub enum Node {
    Literal(Variable),
    And(Vec<Node>),
    Or(Vec<Node>),
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
    fn flatten(&self) -> Self {
        let result = match self {
            Node::Literal(_) => self.clone(),
            Node::Or(items) => {
                let mut child_items = Vec::new();
                for item in (*items).iter() {
                    child_items.push(item.flatten())
                }
                // A || ( (B&&C) || D )
                // =>  A || (B && C) || D
                let mut or_items = Vec::new();
                for child in child_items {
                    match child {
                        Node::Literal(_) => or_items.push(child),
                        Node::And(_) => or_items.push(child),
                        Node::Or(or_content) => {
                            for o in or_content {
                                or_items.push(o)
                            }
                        }
                        Node::Not(_) => or_items.push(child),
                    }
                }
                Node::Or(or_items)
            }
            Node::And(items) => {
                let mut child_items = Vec::new();
                for item in (*items).iter() {
                    child_items.push(item.flatten())
                }
                let mut and_items = Vec::new();
                for child in child_items {
                    match child {
                        Node::Literal(_) => and_items.push(child),
                        Node::And(and_content) => {
                            for a in and_content.into_iter() {
                                and_items.push(a)
                            }
                        }
                        Node::Or(_) => and_items.push(child),
                        Node::Not(_) => and_items.push(child),
                    }
                }
                Node::And(and_items)
            }
            Node::Not(_) => self.clone(),
        };
        result.compact()
    }

    fn cross_product(&self) -> Self {
        match self {
            Node::Literal(_) => self.clone(),
            Node::Not(_) => self.clone(),
            Node::And(items) => {
                if items.len() < 2 {
                    self.clone()
                } else {
                    // A && (B||C) && ~Q ... && Z=>
                    // (A && (B||C)) && (A && ~Q) .. && (A&&Z) =>
                    // (A&&B || A&&C) && (A && ~Q) .. && (A&&Z)
                    let mut and_items = items.clone();
                    let head = and_items.pop().unwrap();
                    let mut new_items = Vec::new();
                    for item in and_items {
                        let new_node = match item.clone() {
                            Node::Literal(_) => Node::And(vec![head.clone(), item]),
                            Node::Not(_) => Node::And(vec![head.clone(), item]),
                            Node::And(_) => Node::And(vec![head.clone(), item]),
                            Node::Or(items) => {
                                let mut children = Vec::new();
                                for child in items {
                                    children.push(Node::And(vec![head.clone(), child]));
                                }
                                Node::Or(children)
                            }
                        };
                        new_items.push(new_node);
                    }
                    if new_items.len() == 1 {
                        new_items[0].clone().flatten()
                    } else {
                        Node::And(new_items).flatten()
                    }
                }
            }
            Node::Or(items) => {
                if items.len() < 2 {
                    self.clone()
                } else {
                    // A || (B&&C) || ~Q ... || Z=>
                    // (A&&B || A&&C) || (A || ~Q) .. || (A||Z) =>
                    let mut or_items = items.clone();
                    let head = or_items.pop().unwrap();
                    let mut new_items = Vec::new();
                    for item in or_items {
                        let new_node = match item.clone() {
                            Node::Literal(_) => Node::And(vec![head.clone(), item]),
                            Node::Not(_) => Node::And(vec![head.clone(), item]),
                            Node::Or(_) => Node::And(vec![head.clone(), item]),
                            Node::And(items) => {
                                let mut children = Vec::new();
                                for child in items.into_iter() {
                                    children.push(Node::Or(vec![head.clone(), child]));
                                }
                                Node::And(children)
                            }
                        };
                        new_items.push(new_node);
                    }
                    if new_items.len() == 1 {
                        new_items[0].clone().flatten()
                    } else {
                        Node::Or(new_items).flatten()
                    }
                }
            }
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

pub struct TreeBuilder {
    vars: Variables,
}

impl TreeBuilder {
    pub fn new(vars: Variables) -> Self {
        Self { vars }
    }

    pub fn lit(&mut self) -> Node {
        Node::Literal(self.vars.create())
    }

    pub fn and(&self, items: Vec<Node>) -> Node {
        let items = items.iter().map(|f| (*f).to_owned()).collect();
        Node::And(items)
    }

    pub fn or(&self, items: Vec<Node>) -> Node {
        let items = items.iter().map(|f| (*f).to_owned()).collect();
        Node::Or(items)
    }

    pub fn not(&self, item: Node) -> Node {
        match item {
            Node::Not(base) => base.deref().clone(),
            _ => Node::Not(Box::new(item.to_owned())),
        }
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
        let and_node = b.and(vec![node1, node2]);
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
        let or_node = b.or(vec![node1, node2]);
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
        let nested_or = b.or(vec![b.or(vec![lit1.clone()]), lit2, lit1]);
        let nested_or = nested_or.flatten();
        let exp = format!("{}", nested_or);
        assert_eq!(exp, "([1]||[2])");
    }

    #[test]
    fn test_flatten_and() {
        let mut b = TreeBuilder::new(Variables::new());
        let lit1 = b.lit();
        let lit2 = b.lit();
        let nested_and = b.and(vec![b.and(vec![lit1.clone()]), lit2, lit1]);
        let nested_and = nested_and.flatten();
        let exp = format!("{}", nested_and);
        assert_eq!(exp, "([1]&&[2])");
    }

    #[test]
    fn test_cross_product_or() {
        let mut b = TreeBuilder::new(Variables::new());
        let lit1 = b.lit();
        let lit2 = b.lit();
        let lit3 = b.lit();
        let cross = b.or(vec![b.and(vec![lit1.clone(), lit2.clone()]), lit3]);
        let cross = cross.cross_product();
        let exp = format!("{}", cross);
        assert_eq!(exp, "(([2]||[3])&&([1]||[3]))");
    }
    #[test]
    fn test_cross_product_and() {
        let mut b = TreeBuilder::new(Variables::new());
        let lit1 = b.lit();
        let lit2 = b.lit();
        let lit3 = b.lit();
        let cross = b.and(vec![b.or(vec![lit1.clone(), lit2.clone()]), lit3]);
        let cross = cross.cross_product();
        let exp = format!("{}", cross);
        assert_eq!(exp, "(([2]&&[3])||([1]&&[3]))");
    }
}
