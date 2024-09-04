// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_utils::launch;
use std::{path::PathBuf, process::Command};

fn main() {
    if let Err(code) = process(std::env::args().skip(1).collect()) {
        std::process::exit(code);
    }
}

fn setup_command(current_executable_dir: &PathBuf, args: Vec<String>) -> Command {
    let miri = false;

    if miri {
        let mut cmd = Command::new("./x.py");
        cmd.arg("miri");
        cmd.arg("run");
        cmd.arg("--bin");
        cmd.arg("prusti-server-driver");
        if !args.is_empty() {
            cmd.arg("--");
            cmd.args(args);
        }
        cmd.envs(std::env::vars());
        return cmd;
    } else {
        let mut prusti_server_driver_path = current_executable_dir.join("prusti-server-driver");
        if cfg!(windows) {
            prusti_server_driver_path.set_extension("exe");
        }
        let mut cmd = Command::new(prusti_server_driver_path);
        cmd.args(args);
        return cmd;
    }
}

fn process(args: Vec<String>) -> Result<(), i32> {
    let _setup = launch::job::setup().unwrap(); // Kill all subprocesses on kill or Ctrl-C

    let java_home = match std::env::var("JAVA_HOME") {
        Ok(java_home) => PathBuf::from(java_home),
        Err(_) => launch::find_java_home()
            .expect("Failed to find Java home directory. Try setting JAVA_HOME"),
    };

    let current_executable_dir = launch::get_current_executable_dir();

    let mut cmd = setup_command(&current_executable_dir, args);

    // Prevent shadowing of default log behavior.
    cmd.env("DEFAULT_PRUSTI_LOG", "info");

    cmd.env("RUST_BACKTRACE", "1");

    let libjvm_path =
        launch::find_libjvm(&java_home).expect("Failed to find JVM library. Check JAVA_HOME");
    launch::add_to_loader_path(vec![libjvm_path], &mut cmd);

    launch::set_environment_settings(&mut cmd, &current_executable_dir, &java_home);

    cmd.stderr(std::process::Stdio::inherit());
    cmd.stdout(std::process::Stdio::inherit());

    let exit_status = cmd.status().expect("could not run prusti-server-driver");

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}
