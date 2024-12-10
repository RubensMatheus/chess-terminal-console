package br.com.chess.game.boardgame;

public class Position {
    //@ spec_public
    private int row;
    //@ spec_public
    private int column;


    /*@ public normal_behavior
      @     ensures this.row == row;
      @     ensures this.column == column;
      @ pure
      @*/
    public Position(int row, int column) {
        this.row = row;
        this.column = column;
    }

    /*@ public normal_behavior
      @     ensures \result == this.row;
      @ pure
      @*/
    public int getRow() {
        return row;
    }

    /*@ public normal_behavior
      @     ensures \result == this.column;
      @ pure
      @*/
    public int getColumn() {
        return column;
    }

    /*@ public normal_behavior
      @     ensures this.row == row;
      @     assignable this.row;
      @*/
    public void setRow(int row) {
        this.row = row;
    }

    /*@ public normal_behavior
      @     ensures this.column == column;
      @     assignable this.column;
      @*/
    public void setColumn(int column) {
        this.column = column;
    }

    /*@ public normal_behavior
      @     ensures this.row == row;
      @     ensures this.column == column;
      @     assignable this.column, this.row;
      @*/
    public void setValues(int row, int column) {
        this.row = row;
        this.column = column;
    }


    /*@ public normal_behavior
      @     ensures \result.equals(this.row + ", " + this.column);
      @ pure
      @*/
    public String getString() {
        return row + ", " + column;
    }

}
