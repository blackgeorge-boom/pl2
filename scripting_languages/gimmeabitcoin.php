<!DOCTYPE HTML>  

<?php
if ("${_SERVER['QUERY_STRING']}" == "")
  $self = "${_SERVER['PHP_SELF']}";
else
  $self = "${_SERVER['PHP_SELF']}?${_SERVER['QUERY_STRING']}";

session_start();

/* 
 * Keep setting the magic number, each time
 * the user submits a correct answer. A correct
 * answer unsets the 'question', which contains
 * the magic number.
 */
if (!isset($_SESSION['question'])) {
  $_SESSION['question'] = substr(md5(rand()), 4, 4);
  $_SESSION['expected'] = $_SESSION['question'] *
  $_SESSION['question'];
}

/*
 * Set only once per session, the amount that
 * the user "ownes" us.
 */
if (!isset($_SESSION['money'])) {
  $_SESSION['money'] = 2000.00;;
}
?>

<html>
<head>
  <style>
  .error {color: #FF0000;}
</style>
</head>
<body style="background-color:powderblue;">  



  <?php

  $test = substr(md5(rand()), 4, 4);
  echo 'Testing : ' . $test;

  /*
   * This function handles the input retrieved from
   * the forms. It cleans whitespaces, backslashes and
   * prevents cross-site scripting.
   */
  function test_input($data) {
    $data = trim($data);
    $data = stripslashes($data);
    $data = htmlspecialchars($data);
    return $data;
  }

  /*
   * This functions gets the supposed bitcoin and hashes
   * it twice. Then, it retrieves the magic number (first 16 bits)
   * and the value of the bitcoin (second 16 bits).
   */
  function get_data($data) {
    $data = test_input($data);
    $hashed_str = hash('sha256',hex2bin($data));
    $hashed_str = hash('sha256',hex2bin($hashed_str));
    $magic = substr($hashed_str, 0, 4);
    $money = substr($hashed_str, 4, 4);
    $result = array("magic"=>$magic, "money"=>$money);
    return $result;
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
    <!-- Print current "debt" -->
    <span>I'd like to have <?php echo number_format(2000.00, 2);?> euros, you still owe me <?php echo number_format($_SESSION['money'], 2); ?>.</span>
    <br><br>

    <?php

    echo 'Answer needed before post is : ' . $_SESSION['question'];

    /*
     * If there is a submit, retreive the answer,
     * and check if it is a valid bitcoin, by comparing
     * its magic number (first 16 bits) with the sessions'
     * magic number.
     */
    if (isset($_REQUEST['answer'])) {
      $answer = $_REQUEST['answer'];
      $data = get_data($answer);
      echo 'You answered : ' . $data["magic"];
      echo 'Answer needed is : ' . $_SESSION['question'];
      if ($data["magic"] == $_SESSION['question']) {
        unset($_SESSION['question']);
        ?>
        <p>Correct! - You inserted 
          <?php

          /*
           * If it is a valid bitcoin, subtract its value
           * from the session's "debt".
           */
          $money = (string) $data["money"];
          $money = hexdec($money);
          $money = $money / 100;
          echo $money;
          $_SESSION['money'] -= $money;
          echo "<br>" . $_SESSION['money'];
          ?></p>
          <form action="<?php echo $self; ?>">
            <input type="submit" value="Play again!">
          </form>
          <?php
        } else {
          ?>

          <!-- Else print that it is not a valid bitcoin. -->
          <p>This is not a valid bitcoin! :-(</p>
          <form action="<?php echo $self; ?>">
            <input type="submit" value="Try again!">
          </form>
          <?php
        }
      } else {
        ?>
        <!-- Print the current magic code. It remains unchanged until
         --  a successful submit 
         -->
        <span class="question">The magic code is <?php echo $_SESSION['question'] ?></span>
        <br><br>
        <form id="my_form" action="<?php echo $self; ?>">
          <label><input name="answer" size="80"></label>
          <br>
          <input type="submit" value="Submit!">
          <input type="button" value="Reset" onclick="myFunction()">
        </form>
        <?php
      }
      ?>
  </div>

    <!-- Simple function to reset the submission form -->
    <script>
      function myFunction() {
        document.getElementById("my_form").reset();
      }
    </script>

  </body>
  </html>
