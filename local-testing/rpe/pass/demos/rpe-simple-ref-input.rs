fn f<'a, T>(x: &'a mut T) -> &'a mut T {
    let to_return = x;
    to_return
}

fn main(){
}
