use anyhow::{anyhow, Result};
use plonky2::field::{
    goldilocks_field::GoldilocksField,
    types::{Field, PrimeField64},
};
use std::{collections::HashMap, fmt::Debug};

use super::{
    custom_statement::GeneralisedStatement,
    entry::Entry,
    gadget::GadgetID,
    statement::{Statement, StatementOrRef, StatementRef},
    value::ScalarOrVec,
    POD,
};

#[derive(Clone, Debug)]
pub enum Operation<S> {
    None,
    NewEntry(Entry),
    CopyStatement(S),
    EqualityFromEntries(S, S),
    NonequalityFromEntries(S, S),
    GtFromEntries(S, S),
    LtFromEntries(S, S),
    TransitiveEqualityFromStatements(S, S),
    GtToNonequality(S),
    LtToNonequality(S),
    ContainsFromEntries(S, S),
    RenameContainedBy(S, S),
    SumOf(S, S, S),
    ProductOf(S, S, S),
    MaxOf(S, S, S),
}

impl<S: Into<GeneralisedStatement> + Clone> Operation<S> {
    // TODO: Clean up.
    pub(crate) fn project(self) -> Operation<GeneralisedStatement> {
        type Op = Operation<GeneralisedStatement>;
        match self {
            Self::None => Op::None,
            Self::NewEntry(entry) => Op::NewEntry(entry),
            Self::CopyStatement(s) => Op::CopyStatement(s.into()),
            Self::EqualityFromEntries(s1, s2) => Op::EqualityFromEntries(s1.into(), s2.into()),
            Self::NonequalityFromEntries(s1, s2) => {
                Op::NonequalityFromEntries(s1.into(), s2.into())
            }
            Self::GtFromEntries(s1, s2) => Op::GtFromEntries(s1.into(), s2.into()),
            Self::LtFromEntries(s1, s2) => Op::LtFromEntries(s1.into(), s2.into()),
            Self::TransitiveEqualityFromStatements(s1, s2) => {
                Op::TransitiveEqualityFromStatements(s1.into(), s2.into())
            }
            Self::GtToNonequality(s) => Op::GtToNonequality(s.into()),
            Self::LtToNonequality(s) => Op::LtToNonequality(s.into()),
            Self::ContainsFromEntries(s1, s2) => Op::ContainsFromEntries(s1.into(), s2.into()),
            Self::RenameContainedBy(s1, s2) => Op::RenameContainedBy(s1.into(), s2.into()),
            Self::SumOf(s1, s2, s3) => Op::SumOf(s1.into(), s2.into(), s3.into()),
            Self::ProductOf(s1, s2, s3) => Op::ProductOf(s1.into(), s2.into(), s3.into()),
            Self::MaxOf(s1, s2, s3) => Op::MaxOf(s1.into(), s2.into(), s3.into()),
        }
    }

    /// Operation evaluation when statements are directly specified.
    pub fn generalised_eval_with_gadget_id(
        &self,
        gadget_id: GadgetID,
    ) -> Result<GeneralisedStatement> {
        type Op = Operation<GeneralisedStatement>;
        type GS = GeneralisedStatement;
        let ok_primitive = |s| Ok(GeneralisedStatement::Primitive(s));
        match self.clone().project() {
            Op::None => ok_primitive(Statement::None),
            Op::NewEntry(entry) => ok_primitive(Statement::from_entry(&entry, gadget_id)),
            Op::CopyStatement(s) => Ok(s),
            Op::EqualityFromEntries(
                GS::Primitive(Statement::ValueOf(anchkey1, v1)),
                GS::Primitive(Statement::ValueOf(anchkey2, v2)),
            ) if v1 == v2 => ok_primitive(Statement::Equal(anchkey1.clone(), anchkey2.clone())),
            Op::NonequalityFromEntries(
                GS::Primitive(Statement::ValueOf(anchkey1, v1)),
                GS::Primitive(Statement::ValueOf(anchkey2, v2)),
            ) if v1 != v2 => ok_primitive(Statement::NotEqual(anchkey1.clone(), anchkey2.clone())),
            Op::GtFromEntries(
                GS::Primitive(Statement::ValueOf(anchkey1, ScalarOrVec::Scalar(v1))),
                GS::Primitive(Statement::ValueOf(anchkey2, ScalarOrVec::Scalar(v2))),
            ) if v1.to_canonical_u64() > v2.to_canonical_u64() => {
                ok_primitive(Statement::Gt(anchkey1.clone(), anchkey2.clone()))
            }
            Op::LtFromEntries(
                GS::Primitive(Statement::ValueOf(anchkey1, ScalarOrVec::Scalar(v1))),
                GS::Primitive(Statement::ValueOf(anchkey2, ScalarOrVec::Scalar(v2))),
            ) if v1.to_canonical_u64() < v2.to_canonical_u64() => {
                ok_primitive(Statement::Lt(anchkey1.clone(), anchkey2.clone()))
            }
            Op::TransitiveEqualityFromStatements(
                GS::Primitive(Statement::Equal(anchkey1, anchkey2)),
                GS::Primitive(Statement::Equal(anchkey3, anchkey4)),
            ) if anchkey2.eq(&anchkey3) => {
                ok_primitive(Statement::Equal(anchkey1.clone(), anchkey4.clone()))
            }
            Op::GtToNonequality(GS::Primitive(Statement::Gt(anchkey1, anchkey2))) => {
                ok_primitive(Statement::NotEqual(anchkey1.clone(), anchkey2.clone()))
            }
            Op::LtToNonequality(GS::Primitive(Statement::Lt(anchkey1, anchkey2))) => {
                ok_primitive(Statement::NotEqual(anchkey1.clone(), anchkey2.clone()))
            }
            Op::ContainsFromEntries(
                GS::Primitive(Statement::ValueOf(anchkey1, ScalarOrVec::Vector(vec))),
                GS::Primitive(Statement::ValueOf(anchkey2, ScalarOrVec::Scalar(scal))),
            ) if vec.contains(&scal) => {
                ok_primitive(Statement::Contains(anchkey1.clone(), anchkey2.clone()))
            }
            Op::RenameContainedBy(
                GS::Primitive(Statement::Contains(anchkey1, anchkey2)),
                GS::Primitive(Statement::Equal(anchkey3, anchkey4)),
            ) if anchkey1.eq(&anchkey3) => {
                ok_primitive(Statement::Contains(anchkey4.clone(), anchkey2.clone()))
            }
            Op::SumOf(
                GS::Primitive(Statement::ValueOf(anchkey1, ScalarOrVec::Scalar(x1))),
                GS::Primitive(Statement::ValueOf(anchkey2, ScalarOrVec::Scalar(x2))),
                GS::Primitive(Statement::ValueOf(anchkey3, ScalarOrVec::Scalar(x3))),
            ) if x1 == x2 + x3 => ok_primitive(Statement::SumOf(
                anchkey1.clone(),
                anchkey2.clone(),
                anchkey3.clone(),
            )),
            Op::ProductOf(
                GS::Primitive(Statement::ValueOf(anchkey1, ScalarOrVec::Scalar(x1))),
                GS::Primitive(Statement::ValueOf(anchkey2, ScalarOrVec::Scalar(x2))),
                GS::Primitive(Statement::ValueOf(anchkey3, ScalarOrVec::Scalar(x3))),
            ) if x1 == x2 * x3 => ok_primitive(Statement::ProductOf(
                anchkey1.clone(),
                anchkey2.clone(),
                anchkey3.clone(),
            )),
            Op::MaxOf(
                GS::Primitive(Statement::ValueOf(anchkey1, ScalarOrVec::Scalar(x1))),
                GS::Primitive(Statement::ValueOf(anchkey2, ScalarOrVec::Scalar(x2))),
                GS::Primitive(Statement::ValueOf(anchkey3, ScalarOrVec::Scalar(x3))),
            ) if x1.to_canonical_u64()
                == Ord::max(x2.to_canonical_u64(), x3.to_canonical_u64()) =>
            {
                ok_primitive(Statement::MaxOf(
                    anchkey1.clone(),
                    anchkey2.clone(),
                    anchkey3.clone(),
                ))
            }
            _ => Err(anyhow!("Invalid claim: {:?}", self.clone().project())),
        }
    }
}

impl Operation<Statement> {
    /// Operation evaluation when statements are directly specified.
    pub fn eval_with_gadget_id(&self, gadget_id: GadgetID) -> Result<Statement> {
        let gen_output = self.generalised_eval_with_gadget_id(gadget_id)?;

        match gen_output {
            GeneralisedStatement::Primitive(s) => Ok(s),
            _ => Err(anyhow!(
                "Evaluation of primitive deduction {:?} resulted in custom statement {:?}!",
                self,
                gen_output
            )),
        }
    }
}

impl<S: StatementOrRef + Clone> Operation<S> {
    /// Resolution of indirect operation specification.
    pub fn deref_args(&self, table: &S::StatementTable) -> Result<Operation<S::Statement>> {
        type Op<S> = Operation<<S as StatementOrRef>::Statement>;
        match self {
            Self::None => Ok(<Op<S>>::None),
            Self::NewEntry(e) => Ok(<Op<S>>::NewEntry(e.clone())),
            Self::CopyStatement(s) => Ok(<Op<S>>::CopyStatement(s.deref_cloned(table)?)),
            Self::EqualityFromEntries(s1, s2) => Ok(<Op<S>>::EqualityFromEntries(
                s1.deref_cloned(table)?,
                s2.deref_cloned(table)?,
            )),
            Self::NonequalityFromEntries(s1, s2) => Ok(<Op<S>>::NonequalityFromEntries(
                s1.deref_cloned(table)?,
                s2.deref_cloned(table)?,
            )),
            Self::GtFromEntries(s1, s2) => Ok(<Op<S>>::GtFromEntries(
                s1.deref_cloned(table)?,
                s2.deref_cloned(table)?,
            )),
            Self::LtFromEntries(s1, s2) => Ok(<Op<S>>::LtFromEntries(
                s1.deref_cloned(table)?,
                s2.deref_cloned(table)?,
            )),
            Self::TransitiveEqualityFromStatements(s1, s2) => {
                Ok(<Op<S>>::TransitiveEqualityFromStatements(
                    s1.deref_cloned(table)?,
                    s2.deref_cloned(table)?,
                ))
            }
            Self::GtToNonequality(s) => Ok(<Op<S>>::GtToNonequality(s.deref_cloned(table)?)),
            Self::LtToNonequality(s) => Ok(<Op<S>>::LtToNonequality(s.deref_cloned(table)?)),
            Self::ContainsFromEntries(s1, s2) => Ok(<Op<S>>::ContainsFromEntries(
                s1.deref_cloned(table)?,
                s2.deref_cloned(table)?,
            )),
            Self::RenameContainedBy(s1, s2) => Ok(<Op<S>>::RenameContainedBy(
                s1.deref_cloned(table)?,
                s2.deref_cloned(table)?,
            )),
            Self::SumOf(s1, s2, s3) => Ok(<Op<S>>::SumOf(
                s1.deref_cloned(table)?,
                s2.deref_cloned(table)?,
                s3.deref_cloned(table)?,
            )),
            Self::ProductOf(s1, s2, s3) => Ok(<Op<S>>::ProductOf(
                s1.deref_cloned(table)?,
                s2.deref_cloned(table)?,
                s3.deref_cloned(table)?,
            )),
            Self::MaxOf(s1, s2, s3) => Ok(<Op<S>>::MaxOf(
                s1.deref_cloned(table)?,
                s2.deref_cloned(table)?,
                s3.deref_cloned(table)?,
            )),
        }
    }
    /// Opcodes
    pub const NONE: GoldilocksField = GoldilocksField(0);
    pub const NEW_ENTRY: GoldilocksField = GoldilocksField(1);
    pub const COPY_STATEMENT: GoldilocksField = GoldilocksField(2);
    pub const EQUALITY_FROM_ENTRIES: GoldilocksField = GoldilocksField(3);
    pub const NONEQUALITY_FROM_ENTRIES: GoldilocksField = GoldilocksField(4);
    pub const GT_FROM_ENTRIES: GoldilocksField = GoldilocksField(5);
    pub const TRANSITIVE_EQUALITY_FROM_STATEMENTS: GoldilocksField = GoldilocksField(6);
    pub const GT_TO_NONEQUALITY: GoldilocksField = GoldilocksField(7);
    pub const CONTAINS_FROM_ENTRIES: GoldilocksField = GoldilocksField(8);
    pub const RENAME_CONTAINED_BY: GoldilocksField = GoldilocksField(9);
    pub const SUM_OF: GoldilocksField = GoldilocksField(10);
    pub const PRODUCT_OF: GoldilocksField = GoldilocksField(11);
    pub const MAX_OF: GoldilocksField = GoldilocksField(12);
    pub const LT_FROM_ENTRIES: GoldilocksField = GoldilocksField(13);
    pub const LT_TO_NONEQUALITY: GoldilocksField = GoldilocksField(14);

    /// Method specifying opcodes.
    pub fn code(&self) -> GoldilocksField {
        match self {
            Self::None => Self::NONE,
            Self::NewEntry(_) => Self::NEW_ENTRY,
            Self::CopyStatement(_) => Self::COPY_STATEMENT,
            Self::EqualityFromEntries(_, _) => Self::EQUALITY_FROM_ENTRIES,
            Self::NonequalityFromEntries(_, _) => Self::NONEQUALITY_FROM_ENTRIES,
            Self::GtFromEntries(_, _) => Self::GT_FROM_ENTRIES,
            Self::TransitiveEqualityFromStatements(_, _) => {
                Self::TRANSITIVE_EQUALITY_FROM_STATEMENTS
            }
            Self::GtToNonequality(_) => Self::GT_TO_NONEQUALITY,
            Self::ContainsFromEntries(_, _) => Self::CONTAINS_FROM_ENTRIES,
            Self::RenameContainedBy(_, _) => Self::RENAME_CONTAINED_BY,
            Self::SumOf(_, _, _) => Self::SUM_OF,
            Self::ProductOf(_, _, _) => Self::PRODUCT_OF,
            Self::MaxOf(_, _, _) => Self::MAX_OF,
            Self::LtFromEntries(_, _) => Self::LT_FROM_ENTRIES,
            Self::LtToNonequality(_) => Self::LT_TO_NONEQUALITY,
        }
    }
    /// Method specifying operands.
    pub fn operands(&self) -> Vec<&S> {
        match self {
            Self::CopyStatement(s) => vec![s],
            Self::EqualityFromEntries(s1, s2) => vec![s1, s2],
            Self::NonequalityFromEntries(s1, s2) => vec![s1, s2],
            Self::GtFromEntries(s1, s2) => vec![s1, s2],
            Self::TransitiveEqualityFromStatements(s1, s2) => vec![s1, s2],
            Self::GtToNonequality(s) => vec![s],
            Self::ContainsFromEntries(s1, s2) => vec![s1, s2],
            Self::RenameContainedBy(s1, s2) => vec![s1, s2],
            Self::SumOf(s1, s2, s3) => vec![s1, s2, s3],
            Self::ProductOf(s1, s2, s3) => vec![s1, s2, s3],
            Self::MaxOf(s1, s2, s3) => vec![s1, s2, s3],
            _ => vec![],
        }
    }
    /// Method specifying entry
    pub fn entry(&self) -> Result<&Entry> {
        match self {
            Self::NewEntry(e) => Ok(e),
            _ => Err(anyhow!("Operator {:?} does not have an entry.", self)),
        }
    }
    pub fn execute_generalised(
        &self,
        gadget_id: GadgetID,
        table: &S::StatementTable,
    ) -> Result<GeneralisedStatement> {
        self.deref_args(table)?
            .generalised_eval_with_gadget_id(gadget_id)
    }
}

/// Named operation struct
#[derive(Clone, Debug)]
pub struct OperationCmd(pub Operation<StatementRef>, pub String);

impl OperationCmd {
    pub fn new(op: Operation<StatementRef>, out_name: impl Into<String>) -> Self {
        Self(op, out_name.into())
    }
}

impl Operation<StatementRef> {
    pub fn execute(
        &self,
        gadget_id: GadgetID,
        table: &<StatementRef as StatementOrRef>::StatementTable,
    ) -> Result<Statement> {
        self.deref_args(table)?.eval_with_gadget_id(gadget_id)
    }
    /// Representation of operation command as field vector of length
    /// 9 + VL of the form
    /// [code] ++ [pod_num1, statement_num1] ++ [pod_num2,
    ///   statement_num2] ++ [pod_num3, statement_num3] ++ [entry]
    ///   ++ contains_proof,
    /// where `VL` stands for the length of the vector involved in a
    /// `contains` op and we substitute 0s for unused operands and
    /// entries.
    pub fn to_fields<const VL: usize>(
        &self,
        ref_index_map: &HashMap<StatementRef, (usize, usize)>,
        statement_table: &<StatementRef as StatementOrRef>::StatementTable,
    ) -> Result<Vec<GoldilocksField>> {
        let op_code = self.code();
        // Enumerate operands, substitute indices and pad with 0s.
        let operands = self
            .operands()
            .into_iter()
            .map(|s_ref| -> Result<_> {
                let (pod_num, statement_num) = ref_index_map
                    .get(s_ref)
                    .ok_or(anyhow!("Missing statement reference {:?}!", s_ref))?;
                Ok(vec![*pod_num, *statement_num])
            })
            .collect::<Result<Vec<Vec<_>>>>()?;
        let num_operands = operands.len();
        let padded_operands = [
            operands.into_iter().flatten().collect::<Vec<_>>(),
            (0..(2 * (3 - num_operands))).map(|_| 0).collect(),
        ]
        .concat()
        .into_iter()
        .map(|x| GoldilocksField(x as u64))
        .collect::<Vec<_>>();

        // Check for entry.
        let entry = self
            .entry()
            .map_or(vec![GoldilocksField::ZERO; 2], |e| e.to_fields());

        // Check for `contains` op.
        let contains_proof = match self {
            Self::ContainsFromEntries(s_ref, _) => {
                // Look up statement
                let statement = s_ref.deref_cloned(statement_table)?;
                match statement {
                    Statement::ValueOf(_, ScalarOrVec::Vector(v)) => {
                        if v.len() == VL {
                            Ok(v.clone())
                        } else {
                            Err(anyhow!(
                                "Vector {:?} in CONTAINS op is not of length {}.",
                                v,
                                VL
                            ))
                        }
                    }
                    _ => Err(anyhow!(
                        "Improper statement argument to CONTAINS op: {:?}",
                        statement
                    )),
                }
            }
            _ => Ok(vec![GoldilocksField::ZERO; VL]),
        }?;

        Ok([vec![op_code], padded_operands, entry, contains_proof].concat())
    }
}

// Op list type. TODO.
#[allow(dead_code)]
#[derive(Clone, Debug)]
pub struct OpList(pub Vec<OperationCmd>);

#[allow(dead_code)]
impl OpList {
    pub fn sort(&self, pods_list: &[(String, POD)]) -> Self {
        // Map from StatementRef to pair of the form (pod index, statement index)
        let ref_index_map = StatementRef::index_map(pods_list);

        let mut sorted_opcmds = self.0.clone();
        let return_type = |op| {
            Statement::code_to_predicate(GoldilocksField(match op {
                Operation::None => 0,
                Operation::NewEntry(_) => 1,
                Operation::CopyStatement(s_ref) => {
                    let (pod_index, statement_index) = ref_index_map.get(&s_ref).unwrap();
                    pods_list[*pod_index].1.payload.statements_list[*statement_index]
                        .1
                        .code()
                        .to_canonical_u64()
                }
                Operation::EqualityFromEntries(_, _) => 2,
                Operation::NonequalityFromEntries(_, _) => 3,
                Operation::GtFromEntries(_, _) => 4,
                Operation::TransitiveEqualityFromStatements(_, _) => 2,
                Operation::GtToNonequality(_) => 3,
                Operation::ContainsFromEntries(_, _) => 5,
                Operation::RenameContainedBy(_, _) => 5,
                Operation::SumOf(_, _, _) => 6,
                Operation::ProductOf(_, _, _) => 7,
                Operation::MaxOf(_, _, _) => 8,
                Operation::LtFromEntries(_, _) => 9,
                Operation::LtToNonequality(_) => 3,
            }))
        };

        sorted_opcmds.sort_by(|a, b| {
            format!("{}:{}", return_type(a.0.clone()), a.1).cmp(&format!(
                "{}:{}",
                return_type(b.0.clone()),
                b.1
            ))
        });
        Self(sorted_opcmds)
    }
    pub fn pad<const NS: usize>(self) -> Result<Self> {
        let op_list_len = self.0.len();
        if op_list_len > NS {
            return Err(anyhow!(
                "The operation list must contain at most {} operations.",
                NS
            ));
        }
        Ok(Self(
            [
                self.0,
                (op_list_len..NS)
                    .map(|i| OperationCmd(Operation::None, format!("_DUMMY_STATEMENT{}", i)))
                    .collect(),
            ]
            .concat(),
        ))
    }
}
