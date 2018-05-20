<!DOCTYPE HTML>  
<html>
<head>
<style>
.error {color: #FF0000;}
</style>
</head>
<body style="background-color:powderblue;">  

  <?php
  if ("${_SERVER['QUERY_STRING']}" == "")
    $self = "${_SERVER['PHP_SELF']}";
  else
    $self = "${_SERVER['PHP_SELF']}?${_SERVER['QUERY_STRING']}";

  session_start();

  if (!isset($_SESSION['question'])) {
    $_SESSION['question'] = substr(md5(rand()), 4, 4);
    $_SESSION['expected'] = $_SESSION['question'] *
                            $_SESSION['question'];
  }
  ?>

  <?php
  // define variables and set to empty values
  $bitcoin = $hashed_str = "";

  $test = substr(md5(rand()), 4, 4);
  echo $test;

  function test_input($data) {
    $data = trim($data);
    $data = stripslashes($data);
    $data = htmlspecialchars($data);
    return $data;
  }

  function get_magic($data) {
    $data = test_input($data);
    $hashed_str = hash('sha256',hex2bin($data));
    $hashed_str = hash('sha256',hex2bin($hashed_str));
    return substr($hashed_str, 0, 4);
  }
  ?>

<h1> Gimme a bitcoin! </h1>
<div>
<p>For the purpose of this exercise, <span style="color:blue">bitcoins</span> are 256-bit hexadecimal numbers, which, when hashed twice using SHA256, start with the 16-bit <span style="color:blue">magic code</span> given on this page. Notice that the magic code frequently changes.
</p>
<p>
The 16-bits immediately after the magic code represent the bitcoin's <span style="color:blue">value</span>, given in euro cents.
</p>
<p>
Bitcoins are represented in hexadecimal form, as strings of 64 hexadecimal digits.
Magic codes are represented as strings of 4 hexadecimal digits.
</p>
</div>

<div>
  <span style="color:red">Example:</span> If the magic code is 4217, the following string is a bitcoin worth 7.99 euro:
  <span style="background-color:violet">796fae438ebdc83ac3a4e8a071d71b1f0f0eace40d8a5b92bb64b1e9ed746066</span>
</div>

<br>

<div>
  <span>I'd like to have 2000.00 euros, you still owe me ????.</span>
  <br><br>

  <?php
  if (isset($_REQUEST['answer'])) {
    $answer = $_REQUEST['answer'];
    if (get_magic($answer) == $_REQUEST['question']) {
  ?>
  <p>Correct!</p>
  <form action="<?php echo $self; ?>">
    <input type="submit" value="Play again!">
  </form>
  <?php
    } else {
  ?>
  <p>This is not a valid bitcoin! :-(</p>
  <form action="<?php echo $self; ?>">
    <input type="submit" value="Try again!">
  </form>
  <?php
    }
  } else {
  ?>
 <span>The magic code is <?php echo $_SESSION['question'] ?></span>
  <br><br>
 <form id="my_form" action="<?php echo $self; ?>">
  <label><input name="answer" size="80"></label>
  <br>
  <input type="submit" value="Submit!">
  <input type="button" value="Reset" onclick="myFunction()">
</form>
  <?php
   unset($_SESSION['question']);
  }
  ?>
</div>



<?php
echo "<h2>Your Input:</h2>";
echo $hashed_str;
echo "<br>";
?>

<script>
function myFunction() {
    document.getElementById("my_form").reset();
}
</script>

</body>
</html>
