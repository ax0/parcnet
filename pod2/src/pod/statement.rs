use anyhow::{anyhow, Result};
use plonky2::field::{
    goldilocks_field::GoldilocksField,
    types::{Field, PrimeField64},
};
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use std::{collections::HashMap, fmt, fmt::Debug};

use super::{
    custom_statement::GeneralisedStatement,
    entry::Entry,
    gadget::GadgetID,
    origin::Origin,
    util::hash_string_to_field,
    value::{HashableEntryValue, ScalarOrVec},
    POD,
};

#[derive(Clone, Debug, Serialize, Deserialize, Eq, Default)]
pub struct AnchoredKey(pub Origin, pub String);

impl PartialEq for AnchoredKey {
    fn eq(&self, ak: &AnchoredKey) -> bool {
        let AnchoredKey(self_origin, self_key) = self;
        let AnchoredKey(other_origin, other_key) = ak;
        (self_origin.origin_id == other_origin.origin_id) && (self_key == other_key)
    }
}

impl AnchoredKey {
    /// Field representation as a vector of length 3.
    pub fn to_fields(&self) -> Vec<GoldilocksField> {
        let AnchoredKey(origin, key) = self;
        [origin.to_fields(), vec![hash_string_to_field(key)]].concat()
    }
    pub fn remap_origin(
        &self,
        f: &dyn Fn(&str) -> Result<(String, GoldilocksField)>,
    ) -> Result<Self> {
        let AnchoredKey(origin, key) = self;
        Ok(AnchoredKey(origin.remap(f)?, key.clone()))
    }
}

impl fmt::Display for AnchoredKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let AnchoredKey(origin, key) = self;
        if origin.origin_name == "_SELF" {
            write!(f, "{}", key)
        } else {
            write!(f, "{}:{}", origin.origin_name, key)
        }
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Statement::None => write!(f, "None"),
            Statement::ValueOf(key, value) => write!(f, "ValueOf({} = {:?})", key, value),
            Statement::Equal(op1, op2) => write!(f, "Equal({} = {})", op1, op2),
            Statement::NotEqual(op1, op2) => write!(f, "NotEqual({} ≠ {})", op1, op2),
            Statement::Gt(op1, op2) => write!(f, "Gt({} > {})", op1, op2),
            Statement::Lt(op1, op2) => write!(f, "Lt({} > {})", op1, op2),
            Statement::Contains(op1, op2) => write!(f, "Contains({} ∈ {})", op1, op2),
            Statement::SumOf(result, op1, op2) => {
                write!(f, "SumOf({} = {} + {})", result, op1, op2)
            }
            Statement::ProductOf(result, op1, op2) => {
                write!(f, "ProductOf({} = {} × {})", result, op1, op2)
            }
            Statement::MaxOf(result, op1, op2) => {
                write!(f, "MaxOf({} = max({}, {}))", result, op1, op2)
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound(deserialize = "T: DeserializeOwned"))]
pub enum ProtoStatement<T>
where
    T: Clone + Debug + Eq + Serialize + DeserializeOwned,
{
    None,
    ValueOf(T, ScalarOrVec),
    Equal(T, T),
    NotEqual(T, T),
    Gt(T, T),
    Lt(T, T),
    Contains(T, T),
    SumOf(T, T, T),
    ProductOf(T, T, T),
    MaxOf(T, T, T),
}

pub type Statement = ProtoStatement<AnchoredKey>;

impl Statement {
    pub fn from_entry(entry: &Entry, this_gadget_id: GadgetID) -> Self {
        Self::ValueOf(
            AnchoredKey(
                Origin::auto("_SELF".to_string(), this_gadget_id),
                entry.key.to_string(),
            ),
            entry.value.clone(),
        )
    }

    /// Field representation as a vector of length 11.
    /// Each statement is arranged as
    /// [code] ++ anchored_key1 ++ anchored_key2 ++ anchored_key3 ++ [value],
    /// where the leftmost keys are populated first and 0s are substituted in
    /// for empty fields.
    pub fn to_fields(&self) -> Vec<GoldilocksField> {
        [
            vec![self.code()],
            match self {
                Self::None => vec![GoldilocksField::ZERO; 10],
                Self::ValueOf(anchkey, value) => [
                    anchkey.to_fields(),
                    vec![GoldilocksField::ZERO; 6],
                    vec![value.hash_or_value()],
                ]
                .concat(),
                Self::Equal(anchkey1, anchkey2) => [
                    anchkey1.to_fields(),
                    anchkey2.to_fields(),
                    vec![GoldilocksField::ZERO; 4],
                ]
                .concat(),
                Self::NotEqual(anchkey1, anchkey2) => [
                    anchkey1.to_fields(),
                    anchkey2.to_fields(),
                    vec![GoldilocksField::ZERO; 4],
                ]
                .concat(),
                Self::Gt(anchkey1, anchkey2) => [
                    anchkey1.to_fields(),
                    anchkey2.to_fields(),
                    vec![GoldilocksField::ZERO; 4],
                ]
                .concat(),
                Self::Lt(anchkey1, anchkey2) => [
                    anchkey1.to_fields(),
                    anchkey2.to_fields(),
                    vec![GoldilocksField::ZERO; 4],
                ]
                .concat(),
                Self::Contains(anchkey1, anchkey2) => [
                    anchkey1.to_fields(),
                    anchkey2.to_fields(),
                    vec![GoldilocksField::ZERO; 4],
                ]
                .concat(),
                Self::SumOf(anchkey1, anchkey2, anchkey3) => [
                    anchkey1.to_fields(),
                    anchkey2.to_fields(),
                    anchkey3.to_fields(),
                    vec![GoldilocksField::ZERO],
                ]
                .concat(),
                Self::ProductOf(anchkey1, anchkey2, anchkey3) => [
                    anchkey1.to_fields(),
                    anchkey2.to_fields(),
                    anchkey3.to_fields(),
                    vec![GoldilocksField::ZERO],
                ]
                .concat(),
                Self::MaxOf(anchkey1, anchkey2, anchkey3) => [
                    anchkey1.to_fields(),
                    anchkey2.to_fields(),
                    anchkey3.to_fields(),
                    vec![GoldilocksField::ZERO],
                ]
                .concat(),
            },
        ]
        .concat()
    }
    pub fn remap_origins(
        &self,
        f: &dyn Fn(&str) -> Result<(String, GoldilocksField)>,
    ) -> Result<Self> {
        match self {
            Self::None => Ok(Self::None),
            Self::ValueOf(anchkey1, v) => Ok(Self::ValueOf(anchkey1.remap_origin(f)?, v.clone())),
            Self::Equal(anchkey1, anchkey2) => Ok(Self::Equal(
                anchkey1.remap_origin(f)?,
                anchkey2.remap_origin(f)?,
            )),
            Self::NotEqual(anchkey1, anchkey2) => Ok(Self::NotEqual(
                anchkey1.remap_origin(f)?,
                anchkey2.remap_origin(f)?,
            )),
            Self::Gt(anchkey1, anchkey2) => Ok(Self::Gt(
                anchkey1.remap_origin(f)?,
                anchkey2.remap_origin(f)?,
            )),
            Self::Lt(anchkey1, anchkey2) => Ok(Self::Lt(
                anchkey1.remap_origin(f)?,
                anchkey2.remap_origin(f)?,
            )),
            Self::Contains(anchkey1, anchkey2) => Ok(Self::Contains(
                anchkey1.remap_origin(f)?,
                anchkey2.remap_origin(f)?,
            )),
            Self::SumOf(anchkey1, anchkey2, anchkey3) => Ok(Self::SumOf(
                anchkey1.remap_origin(f)?,
                anchkey2.remap_origin(f)?,
                anchkey3.remap_origin(f)?,
            )),
            Self::ProductOf(anchkey1, anchkey2, anchkey3) => Ok(Self::ProductOf(
                anchkey1.remap_origin(f)?,
                anchkey2.remap_origin(f)?,
                anchkey3.remap_origin(f)?,
            )),
            Self::MaxOf(anchkey1, anchkey2, anchkey3) => Ok(Self::MaxOf(
                anchkey1.remap_origin(f)?,
                anchkey2.remap_origin(f)?,
                anchkey3.remap_origin(f)?,
            )),
        }
    }
}

impl<T> ProtoStatement<T>
where
    T: Clone + Debug + Eq + Serialize + DeserializeOwned,
{
    pub fn predicate(&self) -> &'static str {
        match self {
            Self::None => "NONE",
            Self::ValueOf(_, _) => "VALUEOF",
            Self::Equal(_, _) => "EQUAL",
            Self::NotEqual(_, _) => "NOTEQUAL",
            Self::Gt(_, _) => "GT",
            Self::Lt(_, _) => "LT",
            Self::Contains(_, _) => "CONTAINS",
            Self::SumOf(_, _, _) => "SUMOF",
            Self::ProductOf(_, _, _) => "PRODUCTOF",
            Self::MaxOf(_, _, _) => "MAXOF",
        }
    }
    pub fn code_to_predicate(code: GoldilocksField) -> &'static str {
        match code.to_canonical_u64() {
            0 => "NONE",
            1 => "VALUEOF",
            2 => "EQUAL",
            3 => "NOTEQUAL",
            4 => "GT",
            5 => "CONTAINS",
            6 => "SUMOF",
            7 => "PRODUCTOF",
            8 => "MAXOF",
            9 => "LT",
            _ => "",
        }
    }

    // Statement codes
    pub const NONE: GoldilocksField = GoldilocksField::ZERO;
    pub const VALUE_OF: GoldilocksField = GoldilocksField(1);
    pub const EQUAL: GoldilocksField = GoldilocksField(2);
    pub const NOT_EQUAL: GoldilocksField = GoldilocksField(3);
    pub const GT: GoldilocksField = GoldilocksField(4);
    pub const CONTAINS: GoldilocksField = GoldilocksField(5);
    pub const SUM_OF: GoldilocksField = GoldilocksField(6);
    pub const PRODUCT_OF: GoldilocksField = GoldilocksField(7);
    pub const MAX_OF: GoldilocksField = GoldilocksField(8);
    pub const LT: GoldilocksField = GoldilocksField(9);
    pub fn code(&self) -> GoldilocksField {
        match self {
            Self::None => Self::NONE,
            Self::ValueOf(_, _) => Self::VALUE_OF,
            Self::Equal(_, _) => Self::EQUAL,
            Self::NotEqual(_, _) => Self::NOT_EQUAL,
            Self::Gt(_, _) => Self::GT,
            Self::Contains(_, _) => Self::CONTAINS,
            Self::SumOf(_, _, _) => Self::SUM_OF,
            Self::ProductOf(_, _, _) => Self::PRODUCT_OF,
            Self::MaxOf(_, _, _) => Self::MAX_OF,
            Self::Lt(_, _) => Self::LT,
        }
    }

    // Misc helpers
    pub fn value(&self) -> Result<ScalarOrVec> {
        match self {
            Self::ValueOf(_, v) => Ok(v.clone()),
            _ => Err(anyhow!("Statement {:?} does not contain a value.", self)),
        }
    }
    pub fn args(&self) -> Vec<T> {
        match self {
            Self::None => vec![],
            Self::ValueOf(anchkey, _) => vec![anchkey.clone()],
            Self::Equal(anchkey1, anchkey2) => vec![anchkey1.clone(), anchkey2.clone()],
            Self::NotEqual(anchkey1, anchkey2) => vec![anchkey1.clone(), anchkey2.clone()],
            Self::Gt(anchkey1, anchkey2) => vec![anchkey1.clone(), anchkey2.clone()],
            Self::Lt(anchkey1, anchkey2) => vec![anchkey1.clone(), anchkey2.clone()],
            Self::Contains(anchkey1, anchkey2) => vec![anchkey1.clone(), anchkey2.clone()],
            Self::SumOf(anchkey1, anchkey2, anchkey3) => {
                vec![anchkey1.clone(), anchkey2.clone(), anchkey3.clone()]
            }
            Self::ProductOf(anchkey1, anchkey2, anchkey3) => {
                vec![anchkey1.clone(), anchkey2.clone(), anchkey3.clone()]
            }
            Self::MaxOf(anchkey1, anchkey2, anchkey3) => {
                vec![anchkey1.clone(), anchkey2.clone(), anchkey3.clone()]
            }
        }
    }

    // Helper to get the anchored key of a value of statement.
    pub fn value_of_anchored_key(&self) -> Option<T> {
        match self {
            Self::ValueOf(key, _) => Some(key.clone()),
            _ => None,
        }
    }

    // Helper to get the result key if it's a ternary statement.
    pub fn result_anchored_key(&self) -> Option<T> {
        match self {
            Self::SumOf(result, _, _)
            | Self::ProductOf(result, _, _)
            | Self::MaxOf(result, _, _) => Some(result.clone()),
            _ => None,
        }
    }
}

// Statements in operations may either be specified directly or as 'references', where
// a reference could be a hash or a string to be looked up in a table. We define a
// trait for this.
pub trait StatementOrRef: Clone + Debug {
    /// Type of table.
    type StatementTable;

    /// Type of underlying statement
    type Statement: Into<GeneralisedStatement> + Clone + Debug;

    /// Resolution procedure.
    fn deref_cloned(&self, table: &Self::StatementTable) -> Result<Self::Statement>;
}

impl StatementOrRef for Statement {
    type StatementTable = ();
    type Statement = Statement;

    fn deref_cloned(&self, _table: &Self::StatementTable) -> Result<Statement> {
        Ok(self.clone())
    }
}

/// Typical statement ref type.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct StatementRef(pub String, pub String);

impl StatementOrRef for StatementRef {
    type StatementTable = HashMap<String, HashMap<String, Statement>>;
    type Statement = Statement;

    fn deref_cloned(&self, table: &Self::StatementTable) -> Result<Statement> {
        let StatementRef(parent_name, statement_name) = self;
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

impl StatementRef {
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
                            StatementRef(pod_name.clone(), statement_name.clone()),
                            (pod_num, statement_num),
                        )
                    },
                )
            })
            .collect()
    }
}
