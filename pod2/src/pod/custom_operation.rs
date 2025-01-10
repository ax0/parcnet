use anyhow::{anyhow, Result};
use plonky2::field::{
    goldilocks_field::GoldilocksField,
    types::{Field, PrimeField64},
};
use std::{collections::HashMap, fmt::Debug};

use crate::pod::{
    custom_statement::{
        AnchoredKeyPattern, AnonCustomStatement, ConstOrVar, GeneralisedStatementRef,
        ProtoGeneralisedStatement,
    },
    statement::{AnchoredKey, ProtoStatement},
    Origin,
};

use super::{
    custom_statement::{GeneralisedStatement, ProtoCustomStatement},
    entry::Entry,
    gadget::GadgetID,
    statement::{Statement, StatementOrRef, StatementRef},
    value::ScalarOrVec,
    Op, POD,
};

/// A generalised operation is either:
#[derive(Clone, Debug)]
pub enum GeneralisedOperation<S> {
    /// a primitive operation, i.e. an `Operation`, or
    Primitive(Op<S>),
    /// a custom operation, i.e. a named custom statement acting on
    /// its argument list. This custom statement will be specified in
    /// a table.
    DeduceCustom(String, Vec<S>),
}

/// For primitive operations, no proof is necessary. For custom
/// operations, we provide a proof in the form of a sequence (vector)
/// of operations with their respective proofs.
pub type GeneralisedOperationProof<S> = Option<Vec<GeneralisedOperationWithProof<S>>>;

pub(crate) fn bind_proof_vars(
    op_name: &str,
    pf: &[GeneralisedOperationWithProof<GeneralisedStatementRef>],
    statement_table: &mut <GeneralisedStatementRef as StatementOrRef>::StatementTable,
) -> Result<()> {
    let memory_pod_name = format!("#{}", op_name);
    statement_table.insert(memory_pod_name.clone(), HashMap::new());
    pf.iter().try_for_each(|op_with_proof| {
        /*
        Add variable bindings to table if necessary.
         */
        if let GeneralisedOperationWithProof(
            GeneralisedOperation::Primitive(Op::NewEntry(entry)),
            _,
        ) = op_with_proof
        {
            let key = AnchoredKey(
                Origin::auto("_SELF".to_string(), GadgetID::ORACLE),
                entry.key.clone(),
            );
            let statement = GeneralisedStatement::Primitive(Statement::ValueOf(
                key.clone(),
                entry.value.clone(),
            ));
            statement_table
                .get_mut(&memory_pod_name)
                .ok_or(anyhow!("Missing {} entry.", memory_pod_name))?
                .insert(format!("{}:{}", statement.predicate(), key), statement);
            anyhow::Ok(())
        } else {
            Ok(())
        }
    })
}

pub struct GeneralisedOperationWithProof<S>(GeneralisedOperation<S>, GeneralisedOperationProof<S>);
impl<S> GeneralisedOperationWithProof<S> {
    pub fn primitive(op: Op<S>) -> Self {
        Self(GeneralisedOperation::Primitive(op), None)
    }

    pub fn custom(
        op_name: &str,
        arg_list: Vec<S>,
        pf: Vec<GeneralisedOperationWithProof<S>>,
    ) -> Self {
        Self(
            GeneralisedOperation::DeduceCustom(op_name.to_string(), arg_list),
            Some(pf),
        )
    }
}

impl GeneralisedOperationWithProof<GeneralisedStatementRef> {
    pub fn deref_args(
        &self,
        table: &mut <GeneralisedStatementRef as StatementOrRef>::StatementTable,
    ) -> Result<GeneralisedOperationWithProof<GeneralisedStatement>> {
        match self {
            Self(GeneralisedOperation::Primitive(op), None) => op.deref_args(table).map(|o| {
                GeneralisedOperationWithProof::<GeneralisedStatement>(
                    GeneralisedOperation::Primitive(o),
                    None,
                )
            }),
            Self(GeneralisedOperation::DeduceCustom(op_name, op_args), Some(pf)) => {
                bind_proof_vars(op_name, pf, table)?;

                let de_args = op_args
                    .iter()
                    .map(|arg| arg.deref_cloned(table))
                    .collect::<Result<Vec<_>>>()?;
                pf.iter()
                    .map(|op_with_proof| op_with_proof.deref_args(table))
                    .collect::<Result<Vec<GeneralisedOperationWithProof<GeneralisedStatement>>>>()
                    .map(|pf| {
                        GeneralisedOperationWithProof::<GeneralisedStatement>(
                            GeneralisedOperation::DeduceCustom(op_name.to_string(), de_args),
                            Some(pf),
                        )
                    })
            }
            Self(GeneralisedOperation::Primitive(_), _) => {
                Err(anyhow!("Primitive operations require no proof."))
            }
            Self(GeneralisedOperation::DeduceCustom(_, _), None) => {
                Err(anyhow!("Custom operations require proofs."))
            }
        }
    }
    pub fn execute(
        &self,
        gadget_id: GadgetID,
        statement_table: &<GeneralisedStatementRef as StatementOrRef>::StatementTable,
        operation_table: &HashMap<String, ProtoCustomStatement>,
    ) -> Result<GeneralisedStatement> {
        let mut statement_table = statement_table.clone();
        self.deref_args(&mut statement_table)?
            .project()
            .eval_with_gadget_id(gadget_id, operation_table)
    }
}

impl<S: Into<GeneralisedStatement> + Clone + Debug> GeneralisedOperationWithProof<S> {
    fn project(&self) -> GeneralisedOperationWithProof<GeneralisedStatement> {
        let pf = &self.1;
        let projected_pf = pf.as_ref().map(|v| {
            v.iter()
                .map(|op_with_pf| op_with_pf.project())
                .collect::<Vec<_>>()
        });
        match self {
            Self(GeneralisedOperation::Primitive(op), _) => {
                GeneralisedOperationWithProof::<GeneralisedStatement>(
                    GeneralisedOperation::Primitive(op.clone().project()),
                    projected_pf,
                )
            }
            Self(GeneralisedOperation::DeduceCustom(op_name, op_args), _) => {
                GeneralisedOperationWithProof::<GeneralisedStatement>(
                    GeneralisedOperation::DeduceCustom(
                        op_name.to_string(),
                        op_args.iter().map(|s| s.clone().into()).collect(),
                    ),
                    projected_pf,
                )
            }
        }
    }
}

impl GeneralisedOperationWithProof<GeneralisedStatement> {
    pub fn eval_with_gadget_id(
        &self,
        gadget_id: GadgetID,
        operation_table: &HashMap<String, ProtoCustomStatement>,
    ) -> Result<GeneralisedStatement> {
        match self {
            Self(GeneralisedOperation::Primitive(op), None) => {
                op.generalised_eval_with_gadget_id(gadget_id)
            }
            Self(GeneralisedOperation::DeduceCustom(op_name, op_args), Some(pf)) => {
                let op_prototype = operation_table.get(op_name).ok_or(anyhow!(
                    "Prototype for custom operation {} missing from table.",
                    op_name
                ))?;
                let statement_args = op_args
                    .iter()
                    .map(
                        |arg| match Into::<GeneralisedStatement>::into(arg.clone()) {
                            GeneralisedStatement::Primitive(Statement::ValueOf(anchkey, _)) => {
                                Ok(anchkey)
                            }
                            _ => Err(anyhow!("Invalid argument {:?} to custom operation.", arg)),
                        },
                    )
                    .collect::<Result<Vec<_>>>()?;
                op_prototype.eval(statement_args, operation_table, pf)
            }
            Self(GeneralisedOperation::Primitive(_), _) => {
                Err(anyhow!("Primitive operations require no proof."))
            }
            Self(GeneralisedOperation::DeduceCustom(_, _), None) => {
                Err(anyhow!("Custom operations require proofs."))
            }
        }
    }
}

#[test]
fn custom_op_test() -> Result<()> {
    let protoprimitive = <ProtoGeneralisedStatement<ConstOrVar<AnchoredKeyPattern>>>::Primitive;
    let primitive = GeneralisedStatement::Primitive;

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

    let operation_table = [("ISDOUBLE".to_string(), is_double)]
        .into_iter()
        .collect::<HashMap<_, _>>();

    type X<T> = ConstOrVar<T>;
    type GSR = GeneralisedStatementRef;

    let mut statement_table = HashMap::new();
    statement_table.insert("POD1".to_string(), HashMap::new());
    statement_table.insert("POD2".to_string(), HashMap::new());

    statement_table.get_mut("POD1").ok_or(anyhow!(""))?.insert(
        "Pop".to_string(),
        primitive(Statement::ValueOf(
            crate::pod::statement::AnchoredKey(
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

    let gowp = |x, y| GeneralisedOperationWithProof::<GSR>(x, y);
    type GOp = GeneralisedOperation<GSR>;

    let pf_trace = vec![
        gowp(
            GOp::Primitive(<Op<GSR>>::NewEntry(Entry::new_from_scalar(
                "Constant",
                GoldilocksField(2),
            ))),
            None,
        ),
        gowp(
            GOp::Primitive(<Op<GSR>>::ProductOf(
                GSR::new("POD2", "Pap"),
                GSR::new("#ISDOUBLE", "VALUEOF:Constant"),
                GSR::new("POD1", "Pop"),
            )),
            None,
        ),
    ];

    let op_with_proof = gowp(
        GOp::DeduceCustom(
            "ISDOUBLE".to_string(),
            vec![GSR::new("POD2", "Pap"), GSR::new("POD1", "Pop")],
        ),
        Some(pf_trace),
    );

    op_with_proof.execute(GadgetID::ORACLE, &statement_table, &operation_table)?;

    Ok(())
}
