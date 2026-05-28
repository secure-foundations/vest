use super::common::Analysis;
use crate::vestir::Combinator;

impl<'a> Analysis<'a> {
    pub(crate) fn gen_execs_section(&self, name: &str, _combinator: &Combinator) -> String {
        let info = self.info(name);
        format!(
            "// TODO(execs): emit Parser / Serializer / Prepare impls for {}\n",
            info.names.exec
        )
    }
}
