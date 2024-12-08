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

    /*@ ensures this.row == row;
      @*/
    public void setRow(int row) {
        this.row = row;
    }

    /*@ ensures this.column == column;
      @*/
    public void setColumn(int column) {
        this.column = column;
    }

    /*@ ensures this.row == row;
      @ ensures this.column == column;
      @*/
    public void setValues(int row, int column) {
        this.row = row;
        this.column = column;
    }

    // falar com prof
    @Override
    public String toString() {
        return row + ", " + column;
    }

}
