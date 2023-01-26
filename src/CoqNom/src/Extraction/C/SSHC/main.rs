extern crate ssh_parser;
use ssh_parser::*;
use std::time::{Instant};

static CLIENT_DH_INIT: &'static [u8] = include_bytes!("../assets/dh_init.raw");
static SERVER_DH_REPLY: &'static [u8] = include_bytes!("../assets/dh_reply.raw");
static NEW_KEYS: &'static [u8] = include_bytes!("../assets/new_keys.raw");

fn bench (bytes : &'static [u8], name_test : &str){
    let mut res = parse_ssh_packet(&bytes);
    for _i in 0..100000 {
        res = parse_ssh_packet(&bytes);
    }
    let ite = 10;
    let mut all = 0;
    for _j in 0..ite {
        let now = Instant::now();
        for _i in 0..100000000 {
            res = parse_ssh_packet(&bytes);
        }
        let elapsed_time = now.elapsed();
        all = all + elapsed_time.as_millis();
    }
    println!("{} : {} ms.", name_test,all / ite);
    println!("{:?}",res);
}

fn main() {
    bench(NEW_KEYS, "SSH - New Keys");
    bench(CLIENT_DH_INIT, "SSH - Client DH Init");
    bench(SERVER_DH_REPLY, "SSH - Server DH Reply");
}
