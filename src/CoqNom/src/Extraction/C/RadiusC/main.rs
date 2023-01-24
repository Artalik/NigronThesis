extern crate nom;
extern crate radius_parser;
use radius_parser::*;
use std::time::{Instant};

static IKEV2_INIT_RESP: &'static [u8] = include_bytes!("../assets/radius_access-request.bin");

fn main() {
    let bytes = IKEV2_INIT_RESP;
    let mut res = parse_radius_data(&bytes);
    for _i in 0..100000 {
        res = parse_radius_data(&bytes);
    }
    let ite = 10;
    let mut all = 0;
    for _j in 0..ite {
        let now = Instant::now();
        for _i in 0..100000000 {
            res = parse_radius_data(&bytes);
        }
        let elapsed_time = now.elapsed();
        all = all + elapsed_time.as_millis();
    }
    println!("Temps moyen pour 100 000 000 parsing :  {} ms.", all / ite);
    println!("{:?}",res);
}
