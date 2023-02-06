use clap::{App, AppSettings, ArgMatches, SubCommand};

pub mod beacon;
pub mod contribute;
pub mod export;
pub mod init;
pub mod verify;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("mpc")
        .about("Multi-party computation (MPC) protocol")
        .setting(AppSettings::SubcommandRequiredElseHelp)
        .subcommands(vec![
            init::subcommand().display_order(1),
            contribute::subcommand().display_order(2),
            beacon::subcommand().display_order(3),
            verify::subcommand().display_order(4),
            export::subcommand().display_order(5),
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
