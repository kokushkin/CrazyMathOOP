import * as React from "react";
import "./styles.css";
import { Integer } from "./integers/integer";

export default function App() {
  const one: Integer = new Integer(3);
  const two: Integer = new Integer(6);

  console.log(one.divides(two, new Integer(2)));

  return (
    <div className="App">
      <h1>Hello CodeSandbox</h1>
      <h2>Start editing to see some magic happen!</h2>
      <a href="http://www-users.math.umn.edu/~garrett/m/algebra/notes/Whole.pdf">Book</a>
    </div>
  );
}
