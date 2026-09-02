//! Abstract Syntax Tree for ASN.1 schemas

use std::fmt;

/// Tagging mode for ASN.1 module
#[derive(Debug, Clone, PartialEq)]
pub enum TaggingMode {
    /// EXPLICIT TAGS (default per X.680)
    Explicit,
    /// IMPLICIT TAGS
    Implicit,
    /// AUTOMATIC TAGS
    Automatic,
}

/// An ASN.1 module definition
#[derive(Debug, Clone, PartialEq)]
pub struct Module {
    pub name: String,
    /// Optional module OID (e.g., {iso(1) identified-organization(3) ...})
    pub oid: Option<Vec<String>>,
    /// Tagging mode (defaults to EXPLICIT if not specified)
    pub tagging_mode: Option<TaggingMode>,
    pub imports: Vec<Import>,
    pub exports: Vec<String>,
    pub definitions: Vec<Definition>,
    pub values: Vec<ValueAssignment>,
}

/// Import declaration (IMPORTS ... FROM ModuleName)
#[derive(Debug, Clone, PartialEq)]
pub struct Import {
    /// Types imported from a module
    pub symbols: Vec<String>,
    /// Module name to import from
    pub module_name: String,
}

/// A type definition within a module
#[derive(Debug, Clone, PartialEq)]
pub struct Definition {
    pub name: String,
    pub ty: Type,
}

/// A value assignment within a module (e.g., oidName OBJECT IDENTIFIER ::= { 1 2 3 })
#[derive(Debug, Clone, PartialEq)]
pub struct ValueAssignment {
    pub name: String,
    pub ty: Type,
    pub value: Value,
}

/// ASN.1 value
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// Object identifier value (e.g., { 1 2 3 } or { parent 4 })
    ObjectIdentifier(Vec<OidComponent>),
    /// Integer value
    Integer(i64),
    /// Boolean value
    Boolean(bool),
    /// String value
    String(String),
    /// Reference to a named INTEGER or ENUMERATED value.
    Identifier(String),
}

/// Component of an object identifier value
#[derive(Debug, Clone, PartialEq)]
pub enum OidComponent {
    /// Numeric component (e.g., 1, 2, 3)
    Number(u32),
    /// Named reference to another OID (e.g., id-ce in { id-ce 19 })
    NamedRef(String),
}

/// Named number for INTEGER types (e.g., tcp(6) in INTEGER {tcp(6), udp(17)})
#[derive(Debug, Clone, PartialEq)]
pub struct NamedNumber {
    pub name: String,
    pub value: i64,
}

/// A field in an ASN.1 Information Object Class (X.681 §9)
///
/// Class fields use `&`-prefixed names (e.g., `&id`, `&Value`).
/// They are meta-schema constructs and have no direct DER encoding.
#[derive(Debug, Clone, PartialEq)]
pub struct ClassField {
    /// Field name without the leading `&` (e.g., `"id"`, `"Value"`)
    pub name: String,
    /// Whether the field has the `UNIQUE` qualifier
    pub unique: bool,
    /// Whether the field has the `OPTIONAL` qualifier
    pub optional: bool,
}

/// ASN.1 type
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    /// SEQUENCE type
    Sequence(Vec<SequenceField>),
    /// SEQUENCE OF type with optional size constraint (legacy)
    SequenceOf(Box<Type>, Option<SizeConstraint>),
    /// SET type
    Set(Vec<SequenceField>),
    /// SET OF type with optional size constraint (legacy)
    SetOf(Box<Type>, Option<SizeConstraint>),
    /// CHOICE type
    Choice(Vec<ChoiceVariant>),
    /// Reference to another type
    TypeRef(String),
    /// INTEGER with optional value constraint (legacy) and optional named numbers
    Integer(Option<ValueConstraint>, Vec<NamedNumber>),
    /// ENUMERATED with named values
    Enumerated(Vec<NamedNumber>),
    /// REAL (floating-point number)
    Real,
    /// BOOLEAN
    Boolean,
    /// OCTET STRING with optional size constraint (legacy)
    OctetString(Option<SizeConstraint>),
    /// BIT STRING with optional size constraint (legacy)
    BitString(Option<SizeConstraint>),
    /// OBJECT IDENTIFIER
    ObjectIdentifier,
    /// RELATIVE-OID
    RelativeOid,
    /// NULL
    Null,
    /// UTF8String with optional size constraint (legacy)
    Utf8String(Option<SizeConstraint>),
    /// PrintableString with optional size constraint (legacy)
    PrintableString(Option<SizeConstraint>),
    /// IA5String with optional size constraint (legacy)
    IA5String(Option<SizeConstraint>),
    /// TeletexString (also known as T61String) with optional size constraint
    TeletexString(Option<SizeConstraint>),
    /// UniversalString with optional size constraint
    UniversalString(Option<SizeConstraint>),
    /// BMPString (Basic Multilingual Plane) with optional size constraint
    BmpString(Option<SizeConstraint>),
    /// GeneralString with optional size constraint
    GeneralString(Option<SizeConstraint>),
    /// NumericString with optional size constraint
    NumericString(Option<SizeConstraint>),
    /// VisibleString with optional size constraint
    VisibleString(Option<SizeConstraint>),
    /// UTCTime
    UtcTime,
    /// GeneralizedTime
    GeneralizedTime,
    /// Tagged type
    Tagged { tag: TagInfo, inner: Box<Type> },
    /// Constrained type (X.680 compliant)
    Constrained {
        base_type: Box<Type>,
        constraint: Constraint,
    },
    /// ANY type (legacy ASN.1, used for extensibility)
    Any,
    /// ANY DEFINED BY field (legacy ASN.1, value depends on another field)
    AnyDefinedBy(String),
    /// ASN.1 Information Object Class definition (X.681 §9)
    ///
    /// `NAME ::= CLASS { &field TYPE [UNIQUE] [OPTIONAL], ... } [WITH SYNTAX { ... }]`
    ///
    /// Classes are meta-schema constructs used to constrain parameterized types.
    /// They have no DER encoding and generate only a documentation comment in Rust.
    Class(Vec<ClassField>),
}

/// Constraint specification (X.680 compliant)
#[derive(Debug, Clone, PartialEq)]
pub struct Constraint {
    pub spec: ConstraintSpec,
    pub exception: Option<ExceptionSpec>,
}

/// Constraint specification type
#[derive(Debug, Clone, PartialEq)]
pub enum ConstraintSpec {
    /// Subtype constraint (value ranges, size, alphabet, etc.)
    Subtype(SubtypeConstraint),
    /// General constraint (table constraints, user-defined)
    General(GeneralConstraint),
}

/// Subtype constraint (X.680 Section 51)
#[derive(Debug, Clone, PartialEq)]
pub enum SubtypeConstraint {
    /// Single value: INTEGER (42)
    SingleValue(ConstraintValue),

    /// Value range: INTEGER (0..100), INTEGER (MIN..100)
    ValueRange {
        min: ConstraintValue,
        max: ConstraintValue,
    },

    /// Size constraint: OCTET STRING (SIZE (1..64))
    SizeConstraint(Box<SubtypeConstraint>),

    /// Permitted alphabet: IA5String (FROM ("A".."Z"))
    PermittedAlphabet(Vec<CharRange>),

    /// Pattern: IA5String (PATTERN "[0-9]+")
    Pattern(String),

    /// Contained subtype: OCTET STRING (CONTAINING INTEGER)
    ContainedSubtype(Box<Type>),

    /// Inner type constraint: SEQUENCE OF INTEGER (1..100)
    InnerType(Box<SubtypeConstraint>),

    /// Union: (constraint1 | constraint2)
    Union(Vec<SubtypeConstraint>),

    /// Intersection: (constraint1 ^ constraint2)
    Intersection(Vec<SubtypeConstraint>),

    /// Complement: ALL EXCEPT constraint
    Complement(Box<SubtypeConstraint>),

    /// Named bit list for BIT STRING { flag(0), delegFlag(1), ... }
    NamedBitList(Vec<NamedNumber>),
}

/// Constraint value with support for named values and keywords
#[derive(Debug, Clone, PartialEq)]
pub enum ConstraintValue {
    /// Integer literal
    Integer(i64),
    /// Named value reference (e.g., tcp in INTEGER {tcp(6), udp(17)})
    NamedValue(String),
    /// MIN keyword
    Min,
    /// MAX keyword
    Max,
}

/// Character range for alphabet constraints
#[derive(Debug, Clone, PartialEq)]
pub struct CharRange {
    pub min: char,
    pub max: char,
}

/// General constraints (X.680 Section 52)
#[derive(Debug, Clone, PartialEq)]
pub enum GeneralConstraint {
    /// Component relation constraint (table constraint)
    ComponentRelation {
        object_set: String,
        component_refs: Vec<String>,
    },
    /// User-defined constraint
    UserDefined(String),
}

/// Exception specification
#[derive(Debug, Clone, PartialEq)]
pub enum ExceptionSpec {
    /// Exception identifier
    Identifier(String),
    /// Exception value
    Value(ConstraintValue),
}

// Legacy constraint types for backward compatibility during migration
/// Value constraint for INTEGER types (DEPRECATED - use Constraint)
#[derive(Debug, Clone, PartialEq)]
pub enum ValueConstraint {
    /// Single value
    Single(i64),
    /// Range (min..max)
    Range(Option<i64>, Option<i64>),
}

/// Size constraint for strings and sequences (DEPRECATED - use Constraint)
#[derive(Debug, Clone, PartialEq)]
pub enum SizeConstraint {
    /// Fixed size
    Fixed(u64),
    /// Range (min..max)
    Range(Option<u64>, Option<u64>),
}

/// Field in a SEQUENCE or SET
#[derive(Debug, Clone, PartialEq)]
pub struct SequenceField {
    pub name: String,
    pub ty: Type,
    pub optional: bool,
    pub default: Option<String>,
}

/// Variant in a CHOICE
#[derive(Debug, Clone, PartialEq)]
pub struct ChoiceVariant {
    pub name: String,
    pub ty: Type,
}

/// Tag information
#[derive(Debug, Clone, PartialEq)]
pub struct TagInfo {
    pub class: TagClass,
    pub number: u32,
    pub tagging: Tagging,
}

/// Tag class
#[derive(Debug, Clone, PartialEq)]
pub enum TagClass {
    Universal,
    Application,
    ContextSpecific,
    Private,
}

/// Tagging mode
#[derive(Debug, Clone, PartialEq)]
pub enum Tagging {
    Explicit,
    Implicit,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Sequence(_) => write!(f, "SEQUENCE"),
            Type::SequenceOf(inner, _) => write!(f, "SEQUENCE OF {}", inner),
            Type::Set(_) => write!(f, "SET"),
            Type::SetOf(inner, _) => write!(f, "SET OF {}", inner),
            Type::Choice(_) => write!(f, "CHOICE"),
            Type::TypeRef(name) => write!(f, "{}", name),
            Type::Integer(_, _) => write!(f, "INTEGER"),
            Type::Enumerated(_) => write!(f, "ENUMERATED"),
            Type::Real => write!(f, "REAL"),
            Type::Boolean => write!(f, "BOOLEAN"),
            Type::OctetString(_) => write!(f, "OCTET STRING"),
            Type::BitString(_) => write!(f, "BIT STRING"),
            Type::ObjectIdentifier => write!(f, "OBJECT IDENTIFIER"),
            Type::RelativeOid => write!(f, "RELATIVE-OID"),
            Type::Null => write!(f, "NULL"),
            Type::Utf8String(_) => write!(f, "UTF8String"),
            Type::PrintableString(_) => write!(f, "PrintableString"),
            Type::IA5String(_) => write!(f, "IA5String"),
            Type::TeletexString(_) => write!(f, "TeletexString"),
            Type::UniversalString(_) => write!(f, "UniversalString"),
            Type::BmpString(_) => write!(f, "BMPString"),
            Type::GeneralString(_) => write!(f, "GeneralString"),
            Type::NumericString(_) => write!(f, "NumericString"),
            Type::VisibleString(_) => write!(f, "VisibleString"),
            Type::UtcTime => write!(f, "UTCTime"),
            Type::GeneralizedTime => write!(f, "GeneralizedTime"),
            Type::Tagged { tag, inner } => {
                write!(f, "[{}] {:?} {}", tag.number, tag.tagging, inner)
            }
            Type::Constrained { base_type, .. } => {
                write!(f, "{} (constrained)", base_type)
            }
            Type::Any => write!(f, "ANY"),
            Type::AnyDefinedBy(field) => write!(f, "ANY DEFINED BY {}", field),
            Type::Class(fields) => {
                write!(f, "CLASS {{ ")?;
                for (i, field) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "&{}", field.name)?;
                    if field.unique {
                        write!(f, " UNIQUE")?;
                    }
                    if field.optional {
                        write!(f, " OPTIONAL")?;
                    }
                }
                write!(f, " }}")
            }
        }
    }
}
