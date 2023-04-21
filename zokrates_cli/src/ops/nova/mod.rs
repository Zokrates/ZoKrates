use clap::{App, AppSettings, ArgMatches, SubCommand};

pub mod compress;
pub mod prove;
pub mod setup;
pub mod verify;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("nova")
        .about("Nova IVC")
        .setting(AppSettings::SubcommandRequiredElseHelp)
        .subcommands(vec![
            setup::subcommand().display_order(1),
            prove::subcommand().display_order(2),
            compress::subcommand().display_order(3),
            verify::subcommand().display_order(4),
        ])
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    match sub_matches.subcommand() {
        ("setup", Some(sub_matches)) => setup::exec(sub_matches),
        ("prove", Some(sub_matches)) => prove::exec(sub_matches),
        ("compress", Some(sub_matches)) => compress::exec(sub_matches),
        ("verify", Some(sub_matches)) => verify::exec(sub_matches),
        _ => unreachable!(),
    }
}
