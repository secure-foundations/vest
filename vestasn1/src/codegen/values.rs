//! Value types, mapping functions, and value assignments.

use super::*;

impl<'a> Generator<'a> {
    pub(super) fn render_value_declaration(
        &self,
        definition: &Definition,
        output: &mut CodeWriter,
    ) -> Result<(), CodegenError> {
        let names = &self.names[&definition.name];
        let rule = self.rules[&definition.name];
        match &definition.ty {
            Type::Sequence(fields) | Type::Set(fields) => {
                let lifetime = self.borrows[&definition.name];
                output.line(format_args!(
                    "/// Value type for ASN.1 `{}`.",
                    definition.name
                ));
                output.line(format_args!(
                    "pub struct {}{} {{",
                    names.value,
                    lifetime_declaration(lifetime)
                ));
                for field in fields {
                    let mut ty = self.exec_type(&field.ty, "'a", rule)?;
                    if field.optional {
                        ty = format!("Option<{ty}>");
                    }
                    output.line(format_args!(
                        "    pub {}: {},",
                        rust_field_name(&field.name),
                        ty
                    ));
                }
                output.line(format_args!(
                    "}}
"
                ));

                output.line(format_args!("#[verifier::ext_equal]"));
                let spec_field_types = fields
                    .iter()
                    .map(|field| {
                        let ty = self.spec_type(&field.ty)?;
                        Ok(if field.optional {
                            format!("Option<{ty}>")
                        } else {
                            ty
                        })
                    })
                    .collect::<Result<Vec<_>, CodegenError>>()?;
                let spec_parameters = spec_field_types
                    .iter()
                    .enumerate()
                    .map(|(index, ty)| format!("T{index} = {ty}"))
                    .collect::<Vec<_>>();
                output.line(format_args!(
                    "pub struct {}{} {{",
                    names.spec,
                    angle_bracketed(&spec_parameters)
                ));
                for (index, field) in fields.iter().enumerate() {
                    output.line(format_args!(
                        "    pub {}: T{index},",
                        rust_field_name(&field.name),
                    ));
                }
                output.line(format_args!(
                    "}}
"
                ));

                output.line(format_args!(
                    "impl{} DeepView for {}{} {{",
                    impl_lifetime(lifetime),
                    names.value,
                    lifetime_application(lifetime, "'a")
                ));
                output.line(format_args!("    type V = {};", names.spec));
                output.line(format_args!("    #[verifier::opaque]"));
                output.line(format_args!(
                    "    open spec fn deep_view(&self) -> Self::V {{"
                ));
                output.line(format_args!("        {} {{", names.spec));
                for field in fields {
                    let rust_name = rust_field_name(&field.name);
                    output.line(format_args!(
                        "            {rust_name}: self.{rust_name}.deep_view(),"
                    ));
                }
                output.line(format_args!("        }}"));
                output.line(format_args!("    }}"));
                output.line(format_args!(
                    "}}
"
                ));
            }
            Type::Choice(variants) => {
                let lifetime = self.borrows[&definition.name];
                output.line(format_args!(
                    "/// Value type for ASN.1 `{}`.",
                    definition.name
                ));
                output.line(format_args!(
                    "pub enum {}{} {{",
                    names.value,
                    lifetime_declaration(lifetime)
                ));
                for variant in variants {
                    output.line(format_args!(
                        "    {}({}),",
                        rust_variant_name(&variant.name),
                        self.exec_type(&variant.ty, "'a", rule)?
                    ));
                }
                output.line(format_args!(
                    "}}
"
                ));

                output.line(format_args!("#[verifier::ext_equal]"));
                let spec_variant_types = variants
                    .iter()
                    .map(|variant| self.spec_type(&variant.ty))
                    .collect::<Result<Vec<_>, CodegenError>>()?;
                let spec_parameters = spec_variant_types
                    .iter()
                    .enumerate()
                    .map(|(index, ty)| format!("T{index} = {ty}"))
                    .collect::<Vec<_>>();
                output.line(format_args!(
                    "pub enum {}{} {{",
                    names.spec,
                    angle_bracketed(&spec_parameters)
                ));
                for (index, variant) in variants.iter().enumerate() {
                    output.line(format_args!(
                        "    {}(T{index}),",
                        rust_variant_name(&variant.name),
                    ));
                }
                output.line(format_args!(
                    "}}
"
                ));

                output.line(format_args!(
                    "impl{} DeepView for {}{} {{",
                    impl_lifetime(lifetime),
                    names.value,
                    lifetime_application(lifetime, "'a")
                ));
                output.line(format_args!("    type V = {};", names.spec));
                output.line(format_args!("    #[verifier::opaque]"));
                output.line(format_args!(
                    "    open spec fn deep_view(&self) -> Self::V {{"
                ));
                output.line(format_args!("        match self {{"));
                for variant in variants {
                    let variant_name = rust_variant_name(&variant.name);
                    output.line(format_args!("            {}::{variant_name}(value) => {}::{variant_name}(value.deep_view()),",
                        names.value, names.spec
                    ));
                }
                output.line(format_args!("        }}"));
                output.line(format_args!("    }}"));
                output.line(format_args!(
                    "}}
"
                ));
            }
            Type::Enumerated(values) => {
                output.line(format_args!("#[repr(i16)]"));
                output.line(format_args!(
                    "#[derive(Debug, Clone, Copy, PartialEq, Eq, StructuralEq)]"
                ));
                output.line(format_args!("#[verifier::ext_equal]"));
                output.line(format_args!("pub enum {} {{", names.value));
                for value in values {
                    output.line(format_args!(
                        "    {} = {},",
                        rust_variant_name(&value.name),
                        value.value
                    ));
                }
                output.line(format_args!(
                    "}}
"
                ));
                output.line(format_args!("pub type {} = {};", names.spec, names.value));
                output.line(format_args!("impl DeepView for {} {{", names.value));
                output.line(format_args!("    type V = Self;"));
                output.line(format_args!(
                    "    open spec fn deep_view(&self) -> Self::V {{ *self }}"
                ));
                output.line(format_args!("}}"));
                output.line(format_args!("impl DeepViewIdentity for {} {{", names.value));
                output.line(format_args!(
                    "    proof fn lemma_deep_view_identity(&self) {{}}"
                ));
                output.line(format_args!("}}"));
                output.line(format_args!("#[cfg(not(verus_keep_ghost))]"));
                output.line(format_args!(
                    "unsafe impl Structural for {} {{}}
",
                    names.value
                ));
            }
            ty => {
                let lifetime = self.borrows[&definition.name];
                output.line(format_args!(
                    "pub type {}{} = {};",
                    names.value,
                    lifetime_declaration(lifetime),
                    self.exec_type(ty, "'a", rule)?
                ));
                output.line(format_args!(
                    "pub type {} = {};
",
                    names.spec,
                    self.spec_type(ty)?
                ));
            }
        }
        Ok(())
    }

    pub(super) fn render_mapper_declaration(
        &self,
        definition: &Definition,
        output: &mut CodeWriter,
    ) -> Result<(), CodegenError> {
        match &definition.ty {
            Type::Sequence(fields) | Type::Set(fields) => {
                self.render_sequence_mappers(definition, fields, output)
            }
            Type::Choice(variants) => self.render_choice_mappers(definition, variants, output),
            Type::Enumerated(values) => self.render_enumerated_mappers(definition, values, output),
            _ => Ok(()),
        }
    }

    fn render_sequence_mappers(
        &self,
        definition: &Definition,
        fields: &[SequenceField],
        output: &mut CodeWriter,
    ) -> Result<(), CodegenError> {
        let names = &self.names[&definition.name];
        let lifetime = self.borrows[&definition.name];
        let rule = self.rules[&definition.name];
        let mut spec_parts = fields
            .iter()
            .map(|field| {
                let ty = self.spec_type(&field.ty)?;
                Ok(if field.optional {
                    format!("Option<{ty}>")
                } else {
                    ty
                })
            })
            .collect::<Result<Vec<_>, CodegenError>>()?;
        let mut parsed_parts = fields
            .iter()
            .map(|field| {
                let ty = self.exec_type(&field.ty, "'a", rule)?;
                Ok(if field.optional {
                    format!("Option<{ty}>")
                } else {
                    ty
                })
            })
            .collect::<Result<Vec<_>, CodegenError>>()?;
        let mut reverse_parts = fields
            .iter()
            .map(|field| {
                let ty = self.exec_type(&field.ty, "'a", rule)?;
                Ok(if field.default.is_some() {
                    ty
                } else if field.optional {
                    format!("Option<&'x {ty}>")
                } else {
                    format!("&'x {ty}")
                })
            })
            .collect::<Result<Vec<_>, CodegenError>>()?;
        let identifiers = fields
            .iter()
            .map(|field| rust_field_name(&field.name))
            .collect::<Vec<_>>();
        let spec_parameters = (0..fields.len())
            .map(|index| format!("T{index}"))
            .collect::<Vec<_>>();
        let generic_spec = format!("{}{}", names.spec, angle_bracketed(&spec_parameters));
        let mut generic_tuple_parts = spec_parameters.clone();
        generic_tuple_parts.push("()".to_string());
        let generic_tuple = nested_type(&generic_tuple_parts);
        let mut tuple_identifiers = identifiers.clone();
        spec_parts.push("()".to_string());
        parsed_parts.push("()".to_string());
        reverse_parts.push("()".to_string());
        tuple_identifiers.push("_end".to_string());

        output.line(format_args!("#[derive(Clone, Copy)]"));
        output.line(format_args!("pub struct {};", names.forward));
        output.line(format_args!("#[derive(Clone, Copy)]"));
        output.line(format_args!(
            "pub struct {};
",
            names.reverse
        ));
        output.line(format_args!(
            "impl{} {} {{",
            angle_bracketed(&spec_parameters),
            generic_spec
        ));
        output.line(format_args!("    #[verifier::opaque]"));
        output.line(format_args!(
            "    pub open spec fn from_structural(input: {generic_tuple}) -> Self {{"
        ));
        output.line(format_args!(
            "        let {} = input;",
            nested_pattern(&tuple_identifiers)
        ));
        output.line(format_args!("        Self {{"));
        for identifier in &identifiers {
            output.line(format_args!("            {identifier},"));
        }
        output.line(format_args!("        }}"));
        output.line(format_args!("    }}"));
        output.blank_line();
        output.line(format_args!("    #[verifier::opaque]"));
        output.line(format_args!(
            "    pub open spec fn into_structural(self) -> {generic_tuple} {{"
        ));
        let mut generic_expressions = identifiers
            .iter()
            .map(|identifier| format!("self.{identifier}"))
            .collect::<Vec<_>>();
        generic_expressions.push("()".to_string());
        output.line(format_args!(
            "        {}",
            nested_expression(&generic_expressions)
        ));
        output.line(format_args!("    }}"));
        output.blank_line();
        output.line(format_args!("    pub proof fn lemma_from_into(self)"));
        output.line(format_args!(
            "        ensures Self::from_structural(Self::into_structural(self)) == self,"
        ));
        output.line(format_args!("    {{"));
        output.line(format_args!(
            "        reveal({}::from_structural);",
            names.spec
        ));
        output.line(format_args!(
            "        reveal({}::into_structural);",
            names.spec
        ));
        output.line(format_args!("    }}"));
        output.blank_line();
        output.line(format_args!(
            "    pub proof fn lemma_into_from(input: {generic_tuple})"
        ));
        output.line(format_args!(
            "        ensures Self::into_structural(Self::from_structural(input)) == input,"
        ));
        output.line(format_args!("    {{"));
        output.line(format_args!(
            "        reveal({}::from_structural);",
            names.spec
        ));
        output.line(format_args!(
            "        reveal({}::into_structural);",
            names.spec
        ));
        output.line(format_args!("    }}"));
        output.line(format_args!(
            "}}
"
        ));
        output.line(format_args!("impl SpecMap for {} {{", names.forward));
        output.line(format_args!(
            "    type Input = {};",
            nested_type(&spec_parts)
        ));
        output.line(format_args!("    type Output = {};", names.spec));
        output.line(format_args!(
            "    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {{"
        ));
        output.line(format_args!(
            "        {}::from_structural(input)",
            names.spec
        ));
        output.line(format_args!("    }}"));
        output.line(format_args!(
            "}}
"
        ));

        output.line(format_args!("impl SpecMap for {} {{", names.reverse));
        output.line(format_args!("    type Input = {};", names.spec));
        output.line(format_args!(
            "    type Output = {};",
            nested_type(&spec_parts)
        ));
        output.line(format_args!(
            "    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {{"
        ));
        output.line(format_args!("        value.into_structural()"));
        output.line(format_args!("    }}"));
        output.line(format_args!(
            "}}
"
        ));

        output.line(format_args!(
            "impl{} Map<{}> for {} {{",
            impl_lifetime(lifetime),
            nested_type(&parsed_parts),
            names.forward
        ));
        output.line(format_args!(
            "    type O = {}{};",
            names.value,
            lifetime_application(lifetime, "'a")
        ));
        output.line(format_args!(
            "    fn map(&self, input: {}) -> (value: Self::O) {{",
            nested_type(&parsed_parts)
        ));
        output.line(format_args!("        proof {{"));
        output.line(format_args!(
            "            reveal(<{} as DeepView>::deep_view);",
            names.value
        ));
        output.line(format_args!(
            "            reveal({}::from_structural);",
            names.spec
        ));
        output.line(format_args!("        }}"));
        output.line(format_args!(
            "        let {} = input;",
            nested_pattern(&tuple_identifiers)
        ));
        output.line(format_args!("        {} {{", names.value));
        for identifier in &identifiers {
            output.line(format_args!("            {identifier},"));
        }
        output.line(format_args!("        }}"));
        output.line(format_args!("    }}"));
        output.line(format_args!(
            "}}
"
        ));

        let reverse_impl = if lifetime { "impl<'a, 'x>" } else { "impl<'x>" };
        output.line(format_args!(
            "{reverse_impl} Map<&'x {}{}> for {} {{",
            names.value,
            lifetime_application(lifetime, "'a"),
            names.reverse
        ));
        output.line(format_args!(
            "    type O = {};",
            nested_type(&reverse_parts)
        ));
        output.line(format_args!(
            "    fn map(&self, value: &'x {}{}) -> (output: Self::O) {{",
            names.value,
            lifetime_application(lifetime, "'a")
        ));
        output.line(format_args!("        proof {{"));
        output.line(format_args!(
            "            reveal(<{} as DeepView>::deep_view);",
            names.value
        ));
        output.line(format_args!(
            "            reveal({}::into_structural);",
            names.spec
        ));
        output.line(format_args!("        }}"));
        let mut reverse_expressions = fields
            .iter()
            .map(|field| {
                let identifier = rust_field_name(&field.name);
                if field.default.is_some() {
                    format!("value.{identifier}")
                } else if field.optional {
                    format!("value.{identifier}.as_ref()")
                } else {
                    format!("&value.{identifier}")
                }
            })
            .collect::<Vec<_>>();
        reverse_expressions.push("()".to_string());
        output.line(format_args!(
            "        let result = {};",
            nested_expression(&reverse_expressions)
        ));
        output.line(format_args!("        proof {{"));
        output.line(format_args!(
            "            assert(result.deep_view() == value.deep_view().into_structural());"
        ));
        output.line(format_args!("        }}"));
        output.line(format_args!("        result"));
        output.line(format_args!("    }}"));
        output.line(format_args!(
            "}}
"
        ));
        Ok(())
    }

    fn render_choice_mappers(
        &self,
        definition: &Definition,
        variants: &[ChoiceVariant],
        output: &mut CodeWriter,
    ) -> Result<(), CodegenError> {
        let names = &self.names[&definition.name];
        let lifetime = self.borrows[&definition.name];
        let rule = self.rules[&definition.name];
        let spec_parts = variants
            .iter()
            .map(|variant| self.spec_type(&variant.ty))
            .collect::<Result<Vec<_>, _>>()?;
        let parsed_parts = variants
            .iter()
            .map(|variant| self.exec_type(&variant.ty, "'a", rule))
            .collect::<Result<Vec<_>, _>>()?;
        let reverse_parts = parsed_parts
            .iter()
            .map(|ty| format!("&'x {ty}"))
            .collect::<Vec<_>>();
        let spec_parameters = (0..variants.len())
            .map(|index| format!("T{index}"))
            .collect::<Vec<_>>();
        let generic_spec = format!("{}{}", names.spec, angle_bracketed(&spec_parameters));
        let generic_sum = nested_sum_type(&spec_parameters);

        output.line(format_args!("#[derive(Clone, Copy)]"));
        output.line(format_args!("pub struct {};", names.forward));
        output.line(format_args!("#[derive(Clone, Copy)]"));
        output.line(format_args!(
            "pub struct {};
",
            names.reverse
        ));
        output.line(format_args!(
            "impl{} {} {{",
            angle_bracketed(&spec_parameters),
            generic_spec
        ));
        output.line(format_args!("    #[verifier::opaque]"));
        output.line(format_args!(
            "    pub open spec fn from_structural(input: {generic_sum}) -> Self {{"
        ));
        output.line(format_args!("        match input {{"));
        for (index, variant) in variants.iter().enumerate() {
            output.line(format_args!(
                "            {} => Self::{}(value),",
                sum_pattern(index, variants.len(), "value"),
                rust_variant_name(&variant.name)
            ));
        }
        output.line(format_args!("        }}"));
        output.line(format_args!("    }}"));
        output.blank_line();
        output.line(format_args!("    #[verifier::opaque]"));
        output.line(format_args!(
            "    pub open spec fn into_structural(self) -> {generic_sum} {{"
        ));
        output.line(format_args!("        match self {{"));
        for (index, variant) in variants.iter().enumerate() {
            output.line(format_args!(
                "            Self::{}(value) => {},",
                rust_variant_name(&variant.name),
                sum_expression(index, variants.len(), "value")
            ));
        }
        output.line(format_args!("        }}"));
        output.line(format_args!("    }}"));
        output.blank_line();
        output.line(format_args!("    pub proof fn lemma_from_into(self)"));
        output.line(format_args!(
            "        ensures Self::from_structural(Self::into_structural(self)) == self,"
        ));
        output.line(format_args!("    {{"));
        output.line(format_args!(
            "        reveal({}::from_structural);",
            names.spec
        ));
        output.line(format_args!(
            "        reveal({}::into_structural);",
            names.spec
        ));
        output.line(format_args!("        match self {{"));
        for variant in variants {
            output.line(format_args!(
                "            Self::{}(_) => {{}},",
                rust_variant_name(&variant.name)
            ));
        }
        output.line(format_args!("        }}"));
        output.line(format_args!("    }}"));
        output.blank_line();
        output.line(format_args!(
            "    pub proof fn lemma_into_from(input: {generic_sum})"
        ));
        output.line(format_args!(
            "        ensures Self::into_structural(Self::from_structural(input)) == input,"
        ));
        output.line(format_args!("    {{"));
        output.line(format_args!(
            "        reveal({}::from_structural);",
            names.spec
        ));
        output.line(format_args!(
            "        reveal({}::into_structural);",
            names.spec
        ));
        output.line(format_args!("        match input {{"));
        for index in 0..variants.len() {
            output.line(format_args!(
                "            {} => {{}},",
                sum_pattern(index, variants.len(), "_")
            ));
        }
        output.line(format_args!("        }}"));
        output.line(format_args!("    }}"));
        output.line(format_args!(
            "}}
"
        ));
        output.line(format_args!("impl SpecMap for {} {{", names.forward));
        output.line(format_args!(
            "    type Input = {};",
            nested_sum_type(&spec_parts)
        ));
        output.line(format_args!("    type Output = {};", names.spec));
        output.line(format_args!(
            "    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {{"
        ));
        output.line(format_args!(
            "        {}::from_structural(input)",
            names.spec
        ));
        output.line(format_args!("    }}"));
        output.line(format_args!(
            "}}
"
        ));

        output.line(format_args!("impl SpecMap for {} {{", names.reverse));
        output.line(format_args!("    type Input = {};", names.spec));
        output.line(format_args!(
            "    type Output = {};",
            nested_sum_type(&spec_parts)
        ));
        output.line(format_args!(
            "    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {{"
        ));
        output.line(format_args!("        value.into_structural()"));
        output.line(format_args!("    }}"));
        output.line(format_args!(
            "}}
"
        ));

        output.line(format_args!(
            "impl{} Map<{}> for {} {{",
            impl_lifetime(lifetime),
            nested_sum_type(&parsed_parts),
            names.forward
        ));
        output.line(format_args!(
            "    type O = {}{};",
            names.value,
            lifetime_application(lifetime, "'a")
        ));
        output.line(format_args!(
            "    fn map(&self, input: {}) -> (value: Self::O) {{",
            nested_sum_type(&parsed_parts)
        ));
        output.line(format_args!("        proof {{"));
        output.line(format_args!(
            "            reveal(<{} as DeepView>::deep_view);",
            names.value
        ));
        output.line(format_args!(
            "            reveal({}::from_structural);",
            names.spec
        ));
        output.line(format_args!("        }}"));
        output.line(format_args!("        match input {{"));
        for (index, variant) in variants.iter().enumerate() {
            output.line(format_args!(
                "            {} => {}::{}(value),",
                sum_pattern(index, variants.len(), "value"),
                names.value,
                rust_variant_name(&variant.name)
            ));
        }
        output.line(format_args!("        }}"));
        output.line(format_args!("    }}"));
        output.line(format_args!(
            "}}
"
        ));

        let reverse_impl = if lifetime { "impl<'a, 'x>" } else { "impl<'x>" };
        output.line(format_args!(
            "{reverse_impl} Map<&'x {}{}> for {} {{",
            names.value,
            lifetime_application(lifetime, "'a"),
            names.reverse
        ));
        output.line(format_args!(
            "    type O = {};",
            nested_sum_type(&reverse_parts)
        ));
        output.line(format_args!(
            "    fn map(&self, value: &'x {}{}) -> (output: Self::O) {{",
            names.value,
            lifetime_application(lifetime, "'a")
        ));
        output.line(format_args!("        proof {{"));
        output.line(format_args!(
            "            reveal(<{} as DeepView>::deep_view);",
            names.value
        ));
        output.line(format_args!(
            "            reveal({}::into_structural);",
            names.spec
        ));
        output.line(format_args!("        }}"));
        output.line(format_args!("        let result = match value {{"));
        for (index, variant) in variants.iter().enumerate() {
            let variant_name = rust_variant_name(&variant.name);
            output.line(format_args!(
                "            {}::{variant_name}(value) => {},",
                names.value,
                sum_expression(index, variants.len(), "value")
            ));
        }
        output.line(format_args!("        }};"));
        output.line(format_args!("        proof {{"));
        output.line(format_args!(
            "            assert(result.deep_view() == value.deep_view().into_structural());"
        ));
        output.line(format_args!("        }}"));
        output.line(format_args!("        result"));
        output.line(format_args!("    }}"));
        output.line(format_args!(
            "}}
"
        ));
        Ok(())
    }

    fn render_enumerated_mappers(
        &self,
        definition: &Definition,
        values: &[NamedNumber],
        output: &mut CodeWriter,
    ) -> Result<(), CodegenError> {
        let names = &self.names[&definition.name];
        output.line(format_args!("#[derive(Clone, Copy)]"));
        output.line(format_args!("pub struct {};", names.predicate));
        output.line(format_args!(
            "impl SpecPred<i16> for {} {{",
            names.predicate
        ));
        output.line(format_args!(
            "    open spec fn apply(&self, value: i16) -> bool {{"
        ));
        output.line(format_args!(
            "        {}",
            values
                .iter()
                .map(|value| format!("value == {}i16", value.value))
                .collect::<Vec<_>>()
                .join(" || ")
        ));
        output.line(format_args!("    }}"));
        output.line(format_args!("}}"));
        output.line(format_args!("impl Pred<i16> for {} {{", names.predicate));
        output.line(format_args!(
            "    fn test(&self, value: &i16) -> (ok: bool) {{"
        ));
        output.line(format_args!(
            "        {}",
            values
                .iter()
                .map(|value| format!("*value == {}i16", value.value))
                .collect::<Vec<_>>()
                .join(" || ")
        ));
        output.line(format_args!("    }}"));
        output.line(format_args!(
            "}}
"
        ));

        output.line(format_args!("#[derive(Clone, Copy)]"));
        output.line(format_args!("pub struct {};", names.forward));
        output.line(format_args!("#[derive(Clone, Copy)]"));
        output.line(format_args!(
            "pub struct {};
",
            names.reverse
        ));
        output.line(format_args!("impl {} {{", names.value));
        output.line(format_args!("    #[verifier::opaque]"));
        output.line(format_args!(
            "    pub open spec fn from_structural(value: i16) -> Self {{"
        ));
        render_enum_number_match(values, &names.value, output, 8);
        output.line(format_args!("    }}"));
        output.blank_line();
        output.line(format_args!("    #[verifier::opaque]"));
        output.line(format_args!(
            "    pub open spec fn into_structural(self) -> i16 {{"
        ));
        output.line(format_args!("        let value = self;"));
        render_enum_value_match(values, &names.value, output, 8);
        output.line(format_args!("    }}"));
        output.blank_line();
        output.line(format_args!("    pub proof fn lemma_from_into(self)"));
        output.line(format_args!(
            "        ensures Self::from_structural(Self::into_structural(self)) == self,"
        ));
        output.line(format_args!("    {{"));
        output.line(format_args!(
            "        reveal({}::from_structural);",
            names.value
        ));
        output.line(format_args!(
            "        reveal({}::into_structural);",
            names.value
        ));
        output.line(format_args!("        match self {{"));
        for value in values {
            output.line(format_args!(
                "            Self::{} => {{}},",
                rust_variant_name(&value.name)
            ));
        }
        output.line(format_args!("        }}"));
        output.line(format_args!("    }}"));
        output.blank_line();
        output.line(format_args!("    pub proof fn lemma_into_from(input: i16)"));
        output.line(format_args!(
            "        requires {}.apply(input),",
            names.predicate
        ));
        output.line(format_args!(
            "        ensures Self::into_structural(Self::from_structural(input)) == input,"
        ));
        output.line(format_args!("    {{"));
        output.line(format_args!(
            "        reveal({}::from_structural);",
            names.value
        ));
        output.line(format_args!(
            "        reveal({}::into_structural);",
            names.value
        ));
        output.line(format_args!("    }}"));
        output.line(format_args!(
            "}}
"
        ));
        output.line(format_args!("impl SpecMap for {} {{", names.forward));
        output.line(format_args!("    type Input = i16;"));
        output.line(format_args!("    type Output = {};", names.value));
        output.line(format_args!(
            "    open spec fn spec_map(&self, value: i16) -> Self::Output {{"
        ));
        output.line(format_args!(
            "        {}::from_structural(value)",
            names.value
        ));
        output.line(format_args!("    }}"));
        output.line(format_args!(
            "}}
"
        ));
        output.line(format_args!("impl SpecMap for {} {{", names.reverse));
        output.line(format_args!("    type Input = {};", names.value));
        output.line(format_args!("    type Output = i16;"));
        output.line(format_args!(
            "    open spec fn spec_map(&self, value: Self::Input) -> i16 {{"
        ));
        output.line(format_args!("        value.into_structural()"));
        output.line(format_args!("    }}"));
        output.line(format_args!(
            "}}
"
        ));
        output.line(format_args!("impl Map<i16> for {} {{", names.forward));
        output.line(format_args!("    type O = {};", names.value));
        output.line(format_args!(
            "    fn map(&self, value: i16) -> (output: Self::O) {{"
        ));
        output.line(format_args!("        proof {{"));
        output.line(format_args!(
            "            reveal(<{} as DeepView>::deep_view);",
            names.value
        ));
        output.line(format_args!(
            "            reveal({}::from_structural);",
            names.value
        ));
        output.line(format_args!("        }}"));
        render_enum_number_match(values, &names.value, output, 8);
        output.line(format_args!("    }}"));
        output.line(format_args!(
            "}}
"
        ));
        output.line(format_args!(
            "impl<'a> Map<&'a {}> for {} {{",
            names.value, names.reverse
        ));
        output.line(format_args!("    type O = i16;"));
        output.line(format_args!(
            "    fn map(&self, value: &'a {}) -> (output: i16) {{",
            names.value
        ));
        output.line(format_args!("        proof {{"));
        output.line(format_args!(
            "            reveal(<{} as DeepView>::deep_view);",
            names.value
        ));
        output.line(format_args!(
            "            reveal({}::into_structural);",
            names.value
        ));
        output.line(format_args!("        }}"));
        output.line(format_args!("        match value {{"));
        for value in values {
            output.line(format_args!(
                "            {}::{} => {}i16,",
                names.value,
                rust_variant_name(&value.name),
                value.value
            ));
        }
        output.line(format_args!("        }}"));
        output.line(format_args!("    }}"));
        output.line(format_args!(
            "}}
"
        ));
        Ok(())
    }
    pub(super) fn render_value_constant(
        &self,
        assignment: &SchemaValueAssignment,
        output: &mut CodeWriter,
    ) -> Result<(), CodegenError> {
        let constant = value_const_name(&assignment.name);
        let (base, base_name) = self.resolve_base_type(&assignment.ty, &mut BTreeSet::new())?;
        let declared_type =
            self.exec_type(&assignment.ty, "'static", self.options.encoding_rules)?;
        match (base, &assignment.value) {
            (Type::Boolean, SchemaValue::Boolean(value)) => {
                output.line(format_args!(
                    "pub const {constant}: {declared_type} = {value};"
                ));
            }
            (Type::Integer(_, named), value) => {
                let integer = match value {
                    SchemaValue::Integer(value) => *value,
                    SchemaValue::Identifier(value) => {
                        lookup_named_number(named, value, &assignment.name)?.value
                    }
                    _ => unreachable!("validated integer assignment"),
                };
                match self.integer_repr_for_type(&assignment.ty, &mut BTreeSet::new())? {
                    Some(IntegerRepr::I8) => {
                        output.line(format_args!(
                            "pub const {constant}: {declared_type} = {integer}i8;"
                        ));
                    }
                    Some(IntegerRepr::I16) => {
                        output.line(format_args!(
                            "pub const {constant}: {declared_type} = {integer}i16;"
                        ));
                    }
                    _ => {
                        output.line(format_args!("pub const {constant}: {declared_type} = vest_lib2::asn1::Integer::Small {{ v: {integer}i64 }};"
                        ));
                    }
                }
            }
            (Type::Enumerated(values), value) => {
                let member = match value {
                    SchemaValue::Integer(number) => values
                        .iter()
                        .find(|value| value.value == *number)
                        .expect("validated ENUMERATED number"),
                    SchemaValue::Identifier(name) => {
                        lookup_named_number(values, name, &assignment.name)?
                    }
                    _ => unreachable!("validated ENUMERATED assignment"),
                };
                let enum_definition = base_name.ok_or_else(|| {
                    CodegenError::new(
                        &assignment.name,
                        "ENUMERATED assignment must refer to a named ENUMERATED type",
                    )
                })?;
                let enum_type = &self.names[enum_definition].value;
                output.line(format_args!(
                    "pub const {constant}: {declared_type} = {enum_type}::{};",
                    rust_variant_name(&member.name)
                ));
            }
            _ => unreachable!("value assignment validated before rendering"),
        }
        Ok(())
    }
}
