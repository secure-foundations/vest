mod choice;
mod depend;
// mod dependent;
mod enums;
mod map;
mod pair;
// mod tlv;
mod wireguard;

macro_rules! my_vec {
    // Match against any number of comma-separated expressions.
    ($($x:expr),* $(,)?) => {
        {
            let mut temp_vec = Vec::new();
            // $(temp_vec.push($x);)*
            $(
                temp_vec.push($x);
            )*
            temp_vec
        }
    };
}
pub(crate) use my_vec;
