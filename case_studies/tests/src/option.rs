
#[rr::returns("Some 2")]
fn maybe_fails() -> Option<i32> {
    Some(2)
}

#[rr::returns("Some 4")]
fn get_result() -> Option<i32> {
    let x = maybe_fails()?;
    let y = maybe_fails()?;

    Some(x + y)
}

#[rr::requires("is_Some x")]
#[rr::exists("y")]
#[rr::returns("y")]
fn match_option(x: &Option<i32>) -> i32{
    if let Some(y) = x {
        return *y;
    }
    else {
        return 0;
    }
}


#[rr::verify]
fn result_get_shr(x: &Result<u32, u32>) -> &u32 {
    match x {
        Ok(y) => y,
        Err(y) => y,
    }
}

#[rr::refine_as("Error")]
enum Error {
    MyError,
}

#[rr::returns("Ok 2")]
fn maybe_fails_2() -> Result<i32, Error> {
    if let Some(x) = maybe_fails() {
        Ok(2)
    }
    else {
        Err(Error::MyError)
    }
}


#[rr::returns("Ok 4")]
fn get_result_2() -> Result<i32, Error> {
    let x = maybe_fails_2()?;
    let y = maybe_fails_2()?;

    Ok(x + y)
}

#[rr::ok]
#[rr::requires("False")]
#[rr::ensures("ret < 10")]
fn maybe_fails_3() -> Result<i32, Error> {
    Err(Error::MyError)
}

#[rr::exists("y")]
#[rr::returns("y")]
fn get_result_3() -> Result<i32, Error> {
    let x = maybe_fails_2()?;
    let y = maybe_fails_3()?;

    Ok(x + y)
}
