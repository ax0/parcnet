use std::{collections::HashMap, fmt::Debug, iter::zip};

use anyhow::{anyhow, Result};
use plonky2::field::goldilocks_field::GoldilocksField;
use serde::{de::DeserializeOwned, Deserialize, Serialize};

use super::{
    entry::Entry,
    statement::{AnchoredKey, ProtoStatement, StatementOrRef, StatementRef},
    value::ScalarOrVec,
    Op, Origin, Statement,
};

/// Encapsulates a constant of some type or a named variable. Used in
/// pattern matching.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound(deserialize = "T: DeserializeOwned"))]
pub enum ConstOrVar<T>
where
    T: Clone + Debug + Eq + Serialize + DeserializeOwned,
{
    Const(T),
    Var(String),
}

/// Encapsulates an anchored key pattern.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AnchoredKeyPattern(pub ConstOrVar<Origin>, pub ConstOrVar<String>);

/// Conjunction of statements to form custom statements.
/// TODO: Replace with enum and generalise.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AnonCustomStatement(Vec<ProtoStatement<ConstOrVar<AnchoredKeyPattern>>>);

/// Custom statements as named combinations of names arguments as
/// defined by `AnonCustomStatement`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProtoCustomStatement(String, Vec<String>, AnonCustomStatement);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CustomStatement(String, Vec<AnchoredKey>);

impl ProtoCustomStatement {
    pub fn new<T: Into<String> + Clone>(
        predicate_name: T,
        arg_list: &[T],
        statement_specifier: AnonCustomStatement,
    ) -> ProtoCustomStatement {
        ProtoCustomStatement(
            predicate_name.into(),
            arg_list.iter().map(|x| x.clone().into()).collect(),
            statement_specifier,
        )
    }
    pub fn predicate(&self) -> String {
        self.0.clone()
    }

    pub fn args(&self) -> Vec<String> {
        self.1.clone()
    }
    // TODO: Code as hash.

    /// Validation procedure for a custom statement prototype.
    /// TODO: Replace proof trace with vector of operation traces.
    pub fn eval(
        &self,
        args: Vec<AnchoredKey>,
        statement_table: &<StatementRef as StatementOrRef>::StatementTable,
        proof_trace: Vec<Op<StatementRef>>,
    ) -> Result<CustomStatement> {
        let arg_vars = self.args();
        let memory_pod_name = format!("#{}", self.0);

        let mut statement_table = statement_table.clone();
        statement_table.insert(memory_pod_name.clone(), HashMap::new());

        // Check argument arities.
        if args.len() != arg_vars.len() {
            return Err(anyhow!(
                "Statement arity ({}) does not match number of arguments ({}).",
                arg_vars.len(),
                args.len()
            ));
        }

        // Bind statement args.
        let mut anchkey_bindings = zip(arg_vars, args.clone()).collect::<HashMap<_, _>>();

        // Construct table for key/origin bindings.
        let mut key_bindings: HashMap<String, String> = HashMap::new();
        let mut origin_bindings: HashMap<String, Origin> = HashMap::new();

        // Resolve proof trace.
        let resolved_trace = proof_trace
            .iter()
            .map(|op| {
                let out_statement =
                    op.execute(super::gadget::GadgetID::ORACLE, &statement_table)?;

                // NewEntry statements may be viewed as variable bindings. We inject these (key, value) pairs into the statement table for later reference.
                if out_statement.code() == Statement::VALUE_OF {
                    let key = out_statement
                        .value_of_anchored_key()
                        .ok_or(anyhow!("VALUEOF statement is missing anchored key!"))?
                        .1;
                    statement_table
                        .get_mut(&memory_pod_name)
                        .ok_or(anyhow!("Missing {} entry.", memory_pod_name))?
                        .insert(
                            format!("{}:{}", out_statement.predicate(), key),
                            out_statement.clone(),
                        );
                }

                Ok(out_statement)
            })
            .collect::<Result<Vec<_>>>()?;

        // Check against existing bindings and bind as we go along, throwing if there is a discrepancy.
        zip(self.2 .0.clone(), resolved_trace).try_for_each(|(prototype, resolution)| {
            // Check predicates.
            if prototype.predicate() != resolution.predicate() {
                return Err(anyhow!(
                    "Predicate mismatch: Prototype requires {} while proof trace yields {}.",
                    prototype.predicate(),
                    resolution.predicate()
                ));
            }

            // Check args by resolving each prototype variable in
            // the appropriate table. If it is not present, insert
            // the corresponding arg from the resolved trace, else
            // check that the value present matches up.
            let prototype_args = prototype.args();
            let resolution_args = resolution.args();

            zip(prototype_args, resolution_args).try_for_each(|(proto_arg, arg)| match proto_arg {
                ConstOrVar::Var(anchkey_var) => {
                    assign_var_and_check(anchkey_var, arg, &mut anchkey_bindings)
                }
                ConstOrVar::Const(anchkey_pattern) => match anchkey_pattern {
                    AnchoredKeyPattern(ConstOrVar::Const(origin), ConstOrVar::Const(key))
                        if AnchoredKey(origin.clone(), key.clone()) != arg =>
                    {
                        Err(anyhow!(
                            "Prototype {:?} does not match resolution {}.",
                            prototype,
                            resolution
                        ))
                    },
                    AnchoredKeyPattern(ConstOrVar::Const(origin), ConstOrVar::Var(key_var)) =>
                        if  origin != arg.0 {
                            Err(anyhow!("Origin in prototype {:?} does not match origin in resolution {}.", prototype, resolution))
                        } else {
                            assign_var_and_check(key_var, arg.1, &mut key_bindings)
                        },
                    AnchoredKeyPattern(ConstOrVar::Var(origin_var), ConstOrVar::Const(key)) =>
                        if key != arg.1 {
                            Err(anyhow!("Key in prototype {:?} does not match key in resolution {}.", prototype, resolution))
                        } else {
                            assign_var_and_check(origin_var, arg.0, &mut origin_bindings)
                        }
                    ,
                    AnchoredKeyPattern(ConstOrVar::Var(origin_var), ConstOrVar::Var(key_var)) =>
                        assign_var_and_check(origin_var, arg.0, &mut origin_bindings).and_then(
                            |_|
                            assign_var_and_check(key_var, arg.1, &mut key_bindings)
                            ),
                    _ => Ok(()),

                },
            })
        })?;

        Ok(CustomStatement(self.predicate(), args))
    }
}

/// Adds variable value to table, checking if the variable has been
/// assigned in the process. If the variable has already been
/// assigned, an error is returned.
fn assign_var_and_check<T>(var_name: String, value: T, table: &mut HashMap<String, T>) -> Result<()>
where
    T: Clone + Debug + Eq,
{
    match table.insert(var_name.clone(), value.clone()) {
        Some(other_value) if value != other_value => Err(anyhow!(
            "Value mismatch: The value of variable {} has been set to both {:?} and {:?}!",
            var_name,
            value,
            other_value
        )),
        _ => Ok(()),
    }
}

#[test]
fn custom_statement_test() -> Result<()> {
    let is_double = ProtoCustomStatement::new(
        "ISDOUBLE",
        &["S1", "S2"],
        AnonCustomStatement(vec![
            ProtoStatement::ValueOf(
                ConstOrVar::Var("Constant".to_string()),
                ScalarOrVec::Scalar(GoldilocksField(2)),
            ),
            ProtoStatement::ProductOf(
                ConstOrVar::Var("S1".to_string()),
                ConstOrVar::Var("Constant".to_string()),
                ConstOrVar::Var("S2".to_string()),
            ),
        ]),
    );

    let mut statement_table = HashMap::new();
    statement_table.insert("POD1".to_string(), HashMap::new());
    statement_table.insert("POD2".to_string(), HashMap::new());

    statement_table.get_mut("POD1").ok_or(anyhow!(""))?.insert(
        "Pop".to_string(),
        Statement::ValueOf(
            AnchoredKey(
                Origin {
                    origin_id: GoldilocksField(6),
                    origin_name: "Narnia".to_string(),
                    gadget_id: super::gadget::GadgetID::SCHNORR16,
                },
                "S5".to_string(),
            ),
            ScalarOrVec::Scalar(GoldilocksField(25)),
        ),
    );
    statement_table.get_mut("POD2").ok_or(anyhow!(""))?.insert(
        "Pap".to_string(),
        Statement::ValueOf(
            AnchoredKey(
                Origin {
                    origin_id: GoldilocksField(5),
                    origin_name: "Hades".to_string(),
                    gadget_id: super::gadget::GadgetID::SCHNORR16,
                },
                "S6".to_string(),
            ),
            ScalarOrVec::Scalar(GoldilocksField(50)),
        ),
    );

    let proof_trace = vec![
        <Op<StatementRef>>::NewEntry(Entry::new_from_scalar("Constant", GoldilocksField(2))),
        <Op<StatementRef>>::ProductOf(
            StatementRef::new("POD2", "Pap"),
            StatementRef::new("#ISDOUBLE", "VALUEOF:Constant"),
            StatementRef::new("POD1", "Pop"),
        ),
    ];

    is_double.eval(
        vec![
            AnchoredKey(
                Origin {
                    origin_id: GoldilocksField(5),
                    origin_name: "Hades".to_string(),
                    gadget_id: super::gadget::GadgetID::SCHNORR16,
                },
                "S6".to_string(),
            ),
            AnchoredKey(
                Origin {
                    origin_id: GoldilocksField(6),
                    origin_name: "Narnia".to_string(),
                    gadget_id: super::gadget::GadgetID::SCHNORR16,
                },
                "S5".to_string(),
            ),
        ],
        &statement_table,
        proof_trace,
    )?;

    Ok(())
}
