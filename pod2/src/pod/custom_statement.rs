use std::{collections::HashMap, fmt::Debug, iter::zip};

use anyhow::{anyhow, Result};
use parcnet_pod::pod::value::string_hash;
use plonky2::field::goldilocks_field::GoldilocksField;
use serde::{de::DeserializeOwned, Deserialize, Serialize};

use super::{
    custom_operation::{bind_proof_vars, GeneralisedOperation, GeneralisedOperationWithProof},
    entry::Entry,
    statement::{AnchoredKey, ProtoStatement, StatementOrRef, StatementRef},
    util::hash_string_to_field,
    value::ScalarOrVec,
    Op, Origin, Statement, POD,
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

impl<T> ConstOrVar<T>
where
    T: Clone + Debug + Eq + Serialize + DeserializeOwned,
{
    pub fn constant(t: impl Into<T>) -> Self {
        Self::Const(t.into())
    }

    pub fn variable(var_name: impl Into<String>) -> Self {
        Self::Var(var_name.into())
    }
}

pub type ProtoStatementArgs<T> = Vec<T>;

/// Encapsulates statement arguments.
pub type StatementArgs = ProtoStatementArgs<AnchoredKey>;

/// Encapsulates an anchored key pattern.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AnchoredKeyPattern(pub ConstOrVar<Origin>, pub ConstOrVar<String>);

/// Conjunction of statements to form custom statements.
/// TODO: Replace with enum and generalise.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AnonCustomStatement(pub Vec<ProtoGeneralisedStatement<ConstOrVar<AnchoredKeyPattern>>>);

/// Custom statements as named combinations of names arguments as
/// defined by `AnonCustomStatement`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProtoCustomStatement(String, Vec<String>, AnonCustomStatement);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound(deserialize = "T: DeserializeOwned"))]
pub enum ProtoGeneralisedStatement<T>
where
    T: Clone + Debug + Eq + Serialize + DeserializeOwned,
{
    Primitive(ProtoStatement<T>),
    Custom(String, ProtoStatementArgs<T>),
}

pub type GeneralisedStatement = ProtoGeneralisedStatement<AnchoredKey>;

impl<T> ProtoGeneralisedStatement<T>
where
    T: Clone + Debug + Eq + Serialize + DeserializeOwned,
{
    pub fn args(&self) -> ProtoStatementArgs<T> {
        match self {
            Self::Primitive(s) => s.args(),
            Self::Custom(_, args) => args.clone(),
        }
    }
    pub fn code(&self) -> GoldilocksField {
        match self {
            Self::Primitive(s) => s.code(),
            Self::Custom(statement_name, _) => hash_string_to_field(statement_name),
        }
    }

    pub fn predicate(&self) -> String {
        match self {
            Self::Primitive(s) => s.predicate().into(),
            Self::Custom(statement_name, _) => statement_name.clone(),
        }
    }
}

impl Into<GeneralisedStatement> for Statement {
    fn into(self) -> GeneralisedStatement {
        GeneralisedStatement::Primitive(self)
    }
}

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

    // TODO: Refactor?
    /// Validation procedure for a custom statement prototype with
    /// proof trace specified by reference
    pub fn eval_deref(
        &self,
        args: StatementArgs,
        operation_table: &HashMap<String, ProtoCustomStatement>,
        statement_table: &<GeneralisedStatementRef as StatementOrRef>::StatementTable,
        proof_trace: &[GeneralisedOperationWithProof<GeneralisedStatementRef>],
    ) -> Result<GeneralisedStatement> {
        let mut statement_table = statement_table.clone();
        bind_proof_vars(&self.0, proof_trace, &mut statement_table)?;

        // Dereference proof trace with respect to statement table.
        let de_proof_trace = proof_trace
            .iter()
            .map(|op_with_proof| op_with_proof.deref_args(&mut statement_table))
            .collect::<Result<Vec<_>>>()?;

        self.eval(args, operation_table, &de_proof_trace)
    }

    /// Validation procedure for a custom statement prototype.
    pub fn eval(
        &self,
        args: StatementArgs,
        operation_table: &HashMap<String, ProtoCustomStatement>,
        proof_trace: &[GeneralisedOperationWithProof<GeneralisedStatement>],
    ) -> Result<GeneralisedStatement> {
        let arg_vars = self.args();

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
                    op.eval_with_gadget_id(super::gadget::GadgetID::ORACLE, operation_table)?;

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
                            "Prototype {:?} does not match resolution {:?}.",
                            prototype,
                            resolution
                        ))
                    },
                    AnchoredKeyPattern(ConstOrVar::Const(origin), ConstOrVar::Var(key_var)) =>
                        if  origin != arg.0 {
                            Err(anyhow!("Origin in prototype {:?} does not match origin in resolution {:?}.", prototype, resolution))
                        } else {
                            assign_var_and_check(key_var, arg.1, &mut key_bindings)
                        },
                    AnchoredKeyPattern(ConstOrVar::Var(origin_var), ConstOrVar::Const(key)) =>
                        if key != arg.1 {
                            Err(anyhow!("Key in prototype {:?} does not match key in resolution {:?}.", prototype, resolution))
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

        Ok(GeneralisedStatement::Custom(self.predicate(), args))
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

/// Typical statement ref type.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct GeneralisedStatementRef(pub String, pub String);

impl StatementOrRef for GeneralisedStatementRef {
    type StatementTable = HashMap<String, HashMap<String, GeneralisedStatement>>;
    type Statement = GeneralisedStatement;

    fn deref_cloned(&self, table: &Self::StatementTable) -> Result<GeneralisedStatement> {
        let Self(parent_name, statement_name) = self;
        table
            .get(parent_name)
            .ok_or(anyhow!(
                "Statement parent {} missing from statement table: {:?}",
                parent_name,
                table
            ))?
            .get(statement_name)
            .ok_or(anyhow!(
                "Statement {} with parent {} missing from statement table: {:?}",
                statement_name,
                parent_name,
                table
            ))
            .cloned()
    }
}

impl GeneralisedStatementRef {
    pub fn new(pod_name: impl Into<String>, statement_name: impl Into<String>) -> Self {
        Self(pod_name.into(), statement_name.into())
    }
    pub fn index_map(pods_list: &[(String, POD)]) -> HashMap<Self, (usize, usize)> {
        pods_list
            .iter()
            .enumerate()
            .flat_map(|(pod_num, (pod_name, pod))| {
                pod.payload.statements_list.iter().enumerate().map(
                    move |(statement_num, (statement_name, _))| {
                        (
                            GeneralisedStatementRef(pod_name.clone(), statement_name.clone()),
                            (pod_num, statement_num),
                        )
                    },
                )
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use anyhow::{anyhow, Result};
    use plonky2::field::goldilocks_field::GoldilocksField;

    use crate::pod::{
        custom_operation::{GeneralisedOperation, GeneralisedOperationWithProof},
        entry::Entry,
        gadget::GadgetID,
        statement::{AnchoredKey, ProtoStatement},
        value::ScalarOrVec,
        Op, Origin, Statement,
    };

    use super::{
        AnchoredKeyPattern, AnonCustomStatement, ConstOrVar, GeneralisedStatement,
        GeneralisedStatementRef, ProtoCustomStatement, ProtoGeneralisedStatement,
    };

    #[test]
    fn custom_statement_test() -> Result<()> {
        let protoprimitive = <ProtoGeneralisedStatement<ConstOrVar<AnchoredKeyPattern>>>::Primitive;
        let primitive = GeneralisedStatement::Primitive;

        type X<T> = ConstOrVar<T>;
        type GSR = GeneralisedStatementRef;

        let is_double = ProtoCustomStatement::new(
            "ISDOUBLE",
            &["S1", "S2"],
            AnonCustomStatement(vec![
                protoprimitive(ProtoStatement::ValueOf(
                    X::variable("Constant"),
                    ScalarOrVec::Scalar(GoldilocksField(2)),
                )),
                protoprimitive(ProtoStatement::ProductOf(
                    X::variable("S1"),
                    X::variable("Constant"),
                    X::variable("S2"),
                )),
            ]),
        );

        let mut statement_table = HashMap::new();
        statement_table.insert("POD1".to_string(), HashMap::new());
        statement_table.insert("POD2".to_string(), HashMap::new());

        statement_table.get_mut("POD1").ok_or(anyhow!(""))?.insert(
            "Pop".to_string(),
            primitive(Statement::ValueOf(
                AnchoredKey(
                    Origin {
                        origin_id: GoldilocksField(6),
                        origin_name: "Narnia".to_string(),
                        gadget_id: GadgetID::SCHNORR16,
                    },
                    "S5".to_string(),
                ),
                ScalarOrVec::Scalar(GoldilocksField(25)),
            )),
        );
        statement_table.get_mut("POD2").ok_or(anyhow!(""))?.insert(
            "Pap".to_string(),
            primitive(Statement::ValueOf(
                AnchoredKey(
                    Origin {
                        origin_id: GoldilocksField(5),
                        origin_name: "Hades".to_string(),
                        gadget_id: GadgetID::SCHNORR16,
                    },
                    "S6".to_string(),
                ),
                ScalarOrVec::Scalar(GoldilocksField(50)),
            )),
        );

        let proof_trace = vec![
            GeneralisedOperationWithProof::primitive(<Op<GSR>>::NewEntry(Entry::new_from_scalar(
                "Constant",
                GoldilocksField(2),
            ))),
            GeneralisedOperationWithProof::primitive(<Op<GSR>>::ProductOf(
                GSR::new("POD2", "Pap"),
                GSR::new("#ISDOUBLE", "VALUEOF:Constant"),
                GSR::new("POD1", "Pop"),
            )),
        ];

        is_double.eval_deref(
            vec![
                AnchoredKey(
                    Origin {
                        origin_id: GoldilocksField(5),
                        origin_name: "Hades".to_string(),
                        gadget_id: GadgetID::SCHNORR16,
                    },
                    "S6".to_string(),
                ),
                AnchoredKey(
                    Origin {
                        origin_id: GoldilocksField(6),
                        origin_name: "Narnia".to_string(),
                        gadget_id: GadgetID::SCHNORR16,
                    },
                    "S5".to_string(),
                ),
            ],
            &HashMap::new(),
            &statement_table,
            &proof_trace,
        )?;

        Ok(())
    }

    #[test]
    fn custom_statement_test2() -> Result<()> {
        let protoprimitive = <ProtoGeneralisedStatement<ConstOrVar<AnchoredKeyPattern>>>::Primitive;
        let primitive = GeneralisedStatement::Primitive;
        let protocustom = <ProtoGeneralisedStatement<ConstOrVar<AnchoredKeyPattern>>>::Custom;
        let custom = GeneralisedStatement::Custom;

        type X<T> = ConstOrVar<T>;
        type GSR = GeneralisedStatementRef;

        let eth_dos = ProtoCustomStatement::new(
            "ETHDOS",
            &["Source", "Destination", "Distance"],
            AnonCustomStatement(vec![
                protoprimitive(ProtoStatement::Equal(
                    X::constant(AnchoredKeyPattern(
                        X::variable("AttestationPod"),
                        X::constant("signer"),
                    )),
                    X::variable("Intermediate"),
                )),
                protoprimitive(ProtoStatement::Equal(
                    X::constant(AnchoredKeyPattern(
                        X::variable("AttestationPod"),
                        X::constant("attestation"),
                    )),
                    X::variable("Destination"),
                )),
                protoprimitive(ProtoStatement::ValueOf(
                    X::variable("Constant"),
                    ScalarOrVec::Scalar(GoldilocksField(1)),
                )),
                protoprimitive(ProtoStatement::SumOf(
                    X::variable("Distance"),
                    X::variable("Constant"),
                    X::variable("N"),
                )),
                protocustom(
                    "ETHDOS".to_string(),
                    vec![
                        X::variable("Source"),
                        X::variable("Intermediate"),
                        X::variable("N"),
                    ],
                ),
            ]),
        );

        let mut statement_table = HashMap::new();
        statement_table.insert(
            "_SELF".to_string(),
            [
                (
                    "PubKey".to_string(),
                    primitive(Statement::ValueOf(
                        AnchoredKey(
                            Origin::auto("_SELF".to_string(), crate::pod::gadget::GadgetID::PLONKY),
                            "signer".to_string(),
                        ),
                        ScalarOrVec::Scalar(GoldilocksField(22222222)),
                    )),
                ),
                (
                    "Vitalik".to_string(),
                    primitive(Statement::ValueOf(
                        AnchoredKey(
                            Origin {
                                origin_id: GoldilocksField(4),
                                origin_name: "Brussels".to_string(),
                                gadget_id: GadgetID::SCHNORR16,
                            },
                            "attestation".to_string(),
                        ),
                        ScalarOrVec::Scalar(GoldilocksField(11111111)),
                    )),
                ),
                (
                    "MyETHDoSDistance".to_string(),
                    primitive(Statement::ValueOf(
                        AnchoredKey(
                            Origin::auto("_SELF".to_string(), crate::pod::gadget::GadgetID::PLONKY),
                            "attestation".to_string(),
                        ),
                        ScalarOrVec::Scalar(GoldilocksField(4)),
                    )),
                ),
            ]
            .into_iter()
            .collect::<HashMap<_, _>>(),
        );

        statement_table.insert(
            "AttPOD".to_string(),
            [
                (
                    "SomeStatement".to_string(),
                    primitive(Statement::ValueOf(
                        AnchoredKey(
                            Origin {
                                origin_id: GoldilocksField(6),
                                origin_name: "Narnia".to_string(),
                                gadget_id: GadgetID::SCHNORR16,
                            },
                            "signer".to_string(),
                        ),
                        ScalarOrVec::Scalar(GoldilocksField(88888888)),
                    )),
                ),
                (
                    "SomeOtherStatement".to_string(),
                    primitive(Statement::ValueOf(
                        AnchoredKey(
                            Origin {
                                origin_id: GoldilocksField(6),
                                origin_name: "Narnia".to_string(),
                                gadget_id: GadgetID::SCHNORR16,
                            },
                            "attestation".to_string(),
                        ),
                        ScalarOrVec::Scalar(GoldilocksField(22222222)),
                    )),
                ),
            ]
            .into_iter()
            .collect::<HashMap<_, _>>(),
        );

        statement_table.insert(
            "ETHDoSPOD".to_string(),
            [
                (
                    "Fact".to_string(),
                    custom(
                        "ETHDOS".to_string(),
                        vec![
                            AnchoredKey(
                                Origin {
                                    origin_id: GoldilocksField(4),
                                    origin_name: "Brussels".to_string(),
                                    gadget_id: GadgetID::SCHNORR16,
                                },
                                "source".to_string(),
                            ),
                            AnchoredKey(
                                Origin {
                                    origin_id: GoldilocksField(4),
                                    origin_name: "Brussels".to_string(),
                                    gadget_id: GadgetID::SCHNORR16,
                                },
                                "destination".to_string(),
                            ),
                            AnchoredKey(
                                Origin {
                                    origin_id: GoldilocksField(4),
                                    origin_name: "Brussels".to_string(),
                                    gadget_id: GadgetID::SCHNORR16,
                                },
                                "distance".to_string(),
                            ),
                        ],
                    ),
                ),
                (
                    "Vitalik".to_string(),
                    primitive(Statement::ValueOf(
                        AnchoredKey(
                            Origin {
                                origin_id: GoldilocksField(4),
                                origin_name: "Brussels".to_string(),
                                gadget_id: GadgetID::SCHNORR16,
                            },
                            "source".to_string(),
                        ),
                        ScalarOrVec::Scalar(GoldilocksField(11111111)),
                    )),
                ),
                (
                    "Alice".to_string(),
                    primitive(Statement::ValueOf(
                        AnchoredKey(
                            Origin {
                                origin_id: GoldilocksField(4),
                                origin_name: "Brussels".to_string(),
                                gadget_id: GadgetID::SCHNORR16,
                            },
                            "destination".to_string(),
                        ),
                        ScalarOrVec::Scalar(GoldilocksField(88888888)),
                    )),
                ),
                (
                    "Distance".to_string(),
                    primitive(Statement::ValueOf(
                        AnchoredKey(
                            Origin {
                                origin_id: GoldilocksField(4),
                                origin_name: "Brussels".to_string(),
                                gadget_id: GadgetID::SCHNORR16,
                            },
                            "distance".to_string(),
                        ),
                        ScalarOrVec::Scalar(GoldilocksField(3)),
                    )),
                ),
            ]
            .into_iter()
            .collect::<HashMap<_, _>>(),
        );

        let proof_trace = vec![
            GeneralisedOperationWithProof::primitive(<Op<GSR>>::EqualityFromEntries(
                GSR::new("AttPOD", "SomeStatement"),
                GSR::new("ETHDoSPOD", "Alice"),
            )),
            GeneralisedOperationWithProof::primitive(<Op<GSR>>::EqualityFromEntries(
                GSR::new("AttPOD", "SomeOtherStatement"),
                GSR::new("_SELF", "PubKey"),
            )),
            GeneralisedOperationWithProof::primitive(<Op<GSR>>::NewEntry(Entry::new_from_scalar(
                "Constant",
                GoldilocksField(1),
            ))),
            GeneralisedOperationWithProof::primitive(<Op<GSR>>::SumOf(
                GSR::new("_SELF", "MyETHDoSDistance"),
                GSR::new("#ETHDOS", "VALUEOF:Constant"),
                GSR::new("ETHDoSPOD", "Distance"),
            )),
            GeneralisedOperationWithProof::primitive(<Op<GSR>>::CopyStatement(GSR::new(
                "ETHDoSPOD",
                "Fact",
            ))),
        ];

        eth_dos.eval_deref(
            vec![
                AnchoredKey(
                    Origin {
                        origin_id: GoldilocksField(4),
                        origin_name: "Brussels".to_string(),
                        gadget_id: GadgetID::SCHNORR16,
                    },
                    "source".to_string(),
                ),
                AnchoredKey(
                    Origin::auto("_SELF".to_string(), crate::pod::gadget::GadgetID::PLONKY),
                    "signer".to_string(),
                ),
                AnchoredKey(
                    Origin::auto("_SELF".to_string(), crate::pod::gadget::GadgetID::PLONKY),
                    "attestation".to_string(),
                ),
            ],
            &HashMap::new(),
            &statement_table,
            &proof_trace,
        )?;

        Ok(())
    }
}
