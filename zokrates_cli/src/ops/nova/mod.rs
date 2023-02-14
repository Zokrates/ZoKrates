use clap::{App, ArgMatches, SubCommand, AppSettings};

pub mod prove;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("nova")
        .about("Nova IVC")
        .setting(AppSettings::SubcommandRequiredElseHelp)
        .subcommands(vec![prove::subcommand().display_order(1)])
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    match sub_matches.subcommand() {
        ("prove", Some(sub_matches)) => prove::exec(sub_matches),
        _ => unreachable!(),
    }
}
