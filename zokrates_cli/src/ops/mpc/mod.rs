use clap::{App, ArgMatches, SubCommand};

pub mod beacon;
pub mod contribute;
pub mod export;
pub mod init;
pub mod verify;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("mpc")
        .about("Multi-party contribution (MPC) protocol")
        .subcommands(vec![
            init::subcommand(),
            contribute::subcommand(),
            beacon::subcommand(),
            verify::subcommand(),
            export::subcommand(),
        ])
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    match sub_matches.subcommand() {
        ("init", Some(sub_matches)) => init::exec(sub_matches),
        ("contribute", Some(sub_matches)) => contribute::exec(sub_matches),
        ("beacon", Some(sub_matches)) => beacon::exec(sub_matches),
        ("verify", Some(sub_matches)) => verify::exec(sub_matches),
        ("export", Some(sub_matches)) => export::exec(sub_matches),
        _ => unreachable!(),
    }
}
