use serde::{Deserialize, Serialize};

use crate::VirCtxt;
use std::fmt::{self, Display, Formatter};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Serialize, Deserialize, Hash, Ord, PartialOrd)]
#[serde(transparent)]
pub struct ViperIdent<'vir>(#[serde(with = "crate::serde::serde_str")] &'vir str);

impl Display for ViperIdent<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<'vir> ViperIdent<'vir> {
    pub fn new(ident: &'vir str) -> ViperIdent<'vir> {
        assert!(is_valid_identifier(ident));
        ViperIdent(ident)
    }

    pub fn sanitize(vcx: &'vir VirCtxt<'_>, ident: String) -> ViperIdent<'vir> {
        let ident = Self::sanitize_str(&ident);
        // Just a sanity check, if this fails there is a problem in `sanitize`
        assert!(is_valid_identifier(ident.as_str()));
        ViperIdent(vcx.alloc_str(&ident))
    }

    pub fn sanitize_str(s: &str) -> String {
        s.chars()
            .map(|c| sanitize_char(c).unwrap_or_else(|| c.to_string()))
            .collect()
    }

    pub fn sanitize_with_underscores(s: &str) -> String {
        s.chars()
            .map(|c| {
                if sanitize_char(c).is_some() {
                    "_".to_string()
                } else {
                    c.to_string()
                }
            })
            .collect()
    }

    pub fn to_str(&self) -> &'vir str {
        self.0
    }
}
fn sanitize_char(c: char) -> Option<String> {
    match c {
        '<' => Some("$lt$".to_string()),
        '>' => Some("$gt$".to_string()),
        ' ' => Some("$space$".to_string()),
        ',' => Some("$comma$".to_string()),
        ':' => Some("$colon$".to_string()),
        '[' => Some("$lbracket$".to_string()),
        ']' => Some("$rbracket$".to_string()),
        '(' => Some("$lparen$".to_string()),
        ')' => Some("$rparen$".to_string()),
        '/' => Some("$slash$".to_string()),
        '#' => Some("$pound$".to_string()),
        '~' => Some("$tilde$".to_string()),
        '!' => Some("$bang$".to_string()),
        '@' => Some("$at$".to_string()),
        '&' => Some("$amp$".to_string()),
        '*' => Some("$star$".to_string()),
        '{' => Some("$lbrace$".to_string()),
        '}' => Some("$rbrace$".to_string()),
        _ => None,
    }
}

fn is_valid_identifier(s: &str) -> bool {
    s.trim().len() == s.len() && s.is_ascii() && s.chars().all(|c| sanitize_char(c).is_none())
}
