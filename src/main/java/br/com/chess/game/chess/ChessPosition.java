package br.com.chess.game.chess;

import br.com.chess.game.boardgame.Position;
import br.com.chess.game.chess.exceptions.ChessException;

public class ChessPosition {

    //@ spec_public
    private char column;
    //@ spec_public
    private int row;

    //@ public invariant column >= 'a' && column <= 'h';
    //@ public invariant row >= 1 && row <= 8;

    /*@ public normal_behavior
      @     requires column >= 'a' && column <= 'h';
      @     requires row >= 1 && row <= 8;
      @     ensures this.column == column;
      @     ensures this.row == row;
      @ also
      @ public exceptional_behavior
      @     requires column < 'a' || column > 'h' || row < 1 || row > 8;
      @     signals_only RuntimeException;
      @ pure
      @*/
    public ChessPosition(char column, int row) {
        if(column < 'a' || column > 'h' || row < 1 || row > 8) {
            throw new ChessException("Erro ao instanciar a posição no tabuleiro. Valores validos são de a1 até h8.");
        }
        this.column = column;
        this.row = row;
    }

    /*@ public normal_behavior
     @     ensures \result == this.column;
     @ pure
     @*/
    public char getColumn() {
        return column;
    }

    /*@ public normal_behavior
      @     ensures \result == this.row;
      @ pure
      @*/
    public int getRow() {
        return row;
    }

    /*@ public normal_behavior
      @     requires row >= 1 && row <= 8;
      @     requires column >= 'a' && column <= 'h';
      @     ensures \result.getRow() == (8 - this.row);
      @     ensures \result.getColumn() == (this.column - 'a');
      @     ensures \result.getRow() >= 0 && \result.getRow() < 8;
      @     ensures \result.getColumn() >= 0 && \result.getColumn() < 8;
      @ assignable \nothing;
      @*/
    public Position toPosition() {
        return new Position(8 - row, column - 'a');
    }

    /*@ public normal_behavior
      @     requires position != null;
      @     requires position.getRow() >= 0 && position.getRow() <= 7;
      @     requires position.getColumn() >= 0 && position.getColumn() <= 7;
      @     requires position.getColumn() <= Character.MAX_VALUE - 'a';
      @     requires 8 - position.getRow() <= Integer.MAX_VALUE;
      @     ensures \result != null;
      @     ensures \result.getRow() == 8 - position.getRow();
      @     ensures \result.getColumn() == (char) ('a' + position.getColumn());
      @     assignable \nothing;
      @ also
      @ public normal_behavior
      @     requires position == null;
      @     ensures \result == null;
      @     assignable \nothing;
      @ also
      @ public exceptional_behavior
      @     requires position != null;
      @     requires position.getRow() < 0 || position.getRow() > 7 || position.getColumn() < 0 || position.getColumn() > 7;
      @     requires 'a' + position.getColumn() >= 0;
      @     requires position.getColumn() <= Character.MAX_VALUE - 'a';
      @     requires 8 - position.getRow() <= Integer.MAX_VALUE;
      @     signals_only RuntimeException;
      @     assignable \nothing;
      @*/
    public static /*@ nullable*/ ChessPosition fromPosition(/*@ nullable */Position position) {
        if(position == null) {
            return null;
        }

        return new ChessPosition((char) ('a' + position.getColumn()), 8 - position.getRow());
    }

    /*@ public normal_behavior
      @     ensures \result.equals("" + column + row);
      @ pure
      @*/
    public String getString (){
        return "" + column + row;
    }

}
