use std::collections::{HashMap, VecDeque};

use pico_sat::{and, lit, one_of, solve_all, Node, Variables};
use semver::{Version, VersionReq};

#[derive(Clone)]
struct Dependency(String, VersionReq);

impl Dependency {
    pub fn new(name: &str, version_req: &str) -> Result<Self, semver::Error> {
        Ok(Dependency(
            name.to_string(),
            VersionReq::parse(version_req)?,
        ))
    }
}

#[derive(Clone)]
struct PackageMetadata {
    name: String,
    versions: HashMap<Version, Vec<Dependency>>,
}

impl PackageMetadata {
    pub fn new(name: &str) -> Self {
        PackageMetadata {
            name: name.to_string(),
            versions: HashMap::new(),
        }
    }

    pub fn add_version(
        mut self,
        version: &str,
        dependencies: Vec<Dependency>,
    ) -> Result<Self, semver::Error> {
        self.versions.insert(Version::parse(version)?, dependencies);
        Ok(self)
    }
}

fn add_package(repo: &mut HashMap<String, PackageMetadata>, package: PackageMetadata) {
    repo.insert(package.name.to_owned(), package);
}

fn build_repo() -> Result<HashMap<String, PackageMetadata>, semver::Error> {
    let mut repo = HashMap::new();

    let package_a = PackageMetadata::new("AAA").add_version(
        "1.0.0",
        vec![
            Dependency::new("BBB", ">=1.0")?,
            Dependency::new("CCC", ">=1.0.1")?,
            Dependency::new("DDD", ">=1.0.0")?,
        ],
    )?;

    let package_b = PackageMetadata::new("BBB")
        .add_version("1.0.0", vec![Dependency::new("DDD", "=1.0.0")?])?
        .add_version(
            "1.0.1",
            vec![
                Dependency::new("CCC", ">=1.0.0")?,
                Dependency::new("DDD", "=1.0.2")?,
            ],
        )?;

    let package_c = PackageMetadata::new("CCC")
        .add_version("1.0.0", vec![Dependency::new("DDD", "=1.0.0")?])?
        .add_version("1.0.1", vec![Dependency::new("DDD", "=1.0.1")?])?
        .add_version("1.0.2", vec![Dependency::new("DDD", "=1.0.2")?])?;

    let package_d = PackageMetadata::new("DDD")
        .add_version("1.0.0", vec![])?
        .add_version("1.0.1", vec![])?
        .add_version("1.0.2", vec![])?;

    add_package(&mut repo, package_a);
    add_package(&mut repo, package_b);
    add_package(&mut repo, package_c);
    add_package(&mut repo, package_d);
    Ok(repo)
}

fn package_resolved_node_for(
    name: &String,
    version: &Version,
    repo: &HashMap<String, PackageMetadata>,
    resolved_nodes: &HashMap<(String, Version), Node>,
    import_lit: &HashMap<(String, Version), Node>,
) -> Option<Node> {
    let deps = repo.get(name).unwrap().versions.get(&version).unwrap();

    let mut childs = Vec::new();
    childs.push(
        import_lit
            .get(&(name.to_owned(), version.to_owned()))
            .unwrap()
            .to_owned(),
    );
    for dependency in deps {
        let pkg_name = dependency.0.to_owned();
        let versions: Vec<Version> = repo
            .get(&pkg_name)
            .unwrap()
            .versions
            .keys()
            .cloned()
            .collect();
        let mut version_nodes = Vec::new();
        for version in versions {
            if dependency.1.matches(&version) {
                if let Some(node) = resolved_nodes.get(&(pkg_name.to_owned(), version)) {
                    version_nodes.push(node.to_owned());
                } else {
                    return None; // dependent version resolve node not prepared
                }
            }
        }
        if !version_nodes.is_empty() {
            childs.push(one_of(version_nodes));
        }
    }
    if childs.len() == 1 {
        Some(childs.pop().unwrap())
    } else {
        Some(and(childs.iter().collect()))
    }
}

pub fn main() -> Result<(), semver::Error> {
    let repo = build_repo()?;
    let mut vars = Variables::new();

    let mut import_lit = HashMap::new();
    // create literals for (Name,Version)
    for (pkg_name, metadata) in &repo {
        for (ver, _deps) in &metadata.versions {
            import_lit.insert((pkg_name.to_owned(), ver.to_owned()), lit(vars.create()));
        }
    }
    let mut resolve_queue = VecDeque::new();
    for (pkg_name, metadata) in &repo {
        for (ver, _deps) in &metadata.versions {
            resolve_queue.push_back((pkg_name, ver))
        }
    }
    let mut resolved_nodes = HashMap::new();

    while let Some((name, version)) = resolve_queue.pop_front() {
        print!("building resolved nodes for {:}@{:} ...", name, version);
        if let Some(node) =
            package_resolved_node_for(&name, &version, &repo, &resolved_nodes, &import_lit)
        {
            println!("builded");
            resolved_nodes.insert((name.to_owned(), version.to_owned()), node);
        } else {
            println!("deffered");
            resolve_queue.push_back((name, version))
        }
    }

    let solve_node = resolved_nodes
        .get(&("AAA".to_string(), Version::parse("1.0.0").unwrap()))
        .unwrap();
    let solve_node = solve_node.to_or_and_not_form();
    let count_vars = vars.count();
    let mut solve_formula = solve_node.to_cnf(&mut vars);
    println!("solve_fomula:{:?}", solve_formula);
    let answers = solve_all(&mut solve_formula, count_vars);
    println!("answers:{:?}", answers);
    for _answer in answers {}
    Ok(())
}
