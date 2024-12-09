package br.com.chess.game.boardgame;

import br.com.chess.game.boardgame.exceptions.BoardException;

public class Board {

    //@ spec_public
    private int rows;
    //@ spec_public
    private int columns;
    //@ spec_public
    private /*@ nullable */Piece[][] pieces;

    //@ public invariant rows > 0 && columns > 0;
    //@ public invariant pieces != null;
    //@ public invariant pieces.length == rows;
    //@ public invariant (\forall int i; 0 <= i && i < rows; pieces[i] != null);
    //@ public invariant (\forall int i; 0 <= i && i < rows; pieces[i].length == columns);
    //@ public invariant (\forall int i; 0 <= i && i < rows;  (pieces[i] == null || \elemtype(\typeof(pieces[i])) == \type(Piece)));


    /*@ public normal_behavior
      @     requires rows > 0 && columns > 0;
      @     ensures this.columns == columns;
      @     ensures this.rows == rows;
      @ also
      @ public exceptional_behavior
      @     requires rows < 1 || columns < 1;
      @     signals_only RuntimeException;
      @ pure
      @*/
    public Board(int rows, int columns) {
        if (rows < 1 || columns < 1) {
            throw new BoardException("Erro ao criar o tabuleiro: " +
                    "É necessario que haja pelo menos 1 linha e 1 coluna");
        }
        this.rows = rows;
        this.columns = columns;
        pieces = new Piece[rows][];

        /*@ loop_invariant 0 <= i && i <= rows;
          @ loop_invariant (\forall int k; 0 <= k && k < i; pieces[k] != null && pieces[k].length == columns && \elemtype(\typeof(pieces[k])) == \type(Piece));
          @ decreasing rows - i;
          @*/
        for (int i = 0; i < rows; i++) {
            pieces[i] = new Piece[columns];
        }
    }


    /*@ public normal_behavior
      @     ensures \result == this.rows;
      @ pure
      @*/
    public int getRows() {
        return rows;
    }

    /*@ public normal_behavior
      @     ensures \result == this.columns;
      @ pure
      @*/
    public int getColumns() {
        return columns;
    }

    /*@ public normal_behavior
      @     requires positionExistsBasic(row, column);
      @     ensures \result == pieces[row][column];
      @     assignable \nothing;
      @ also
      @ public exceptional_behavior
      @     requires !positionExistsBasic(row, column);
      @     signals_only RuntimeException;
      @     assignable \nothing;
      @*/
    public /*@ nullable */ Piece piece(int row, int column) {

        if (!positionExistsBasic(row, column)) {
            //@ assert !(row >= 0 && row < rows && column >= 0 && column < columns);
            throw new BoardException("A posição está fora do tabuleiro.");
        }

        //@ assert positionExistsBasic(row, column);
        return pieces[row][column];
    }

    /*@ public normal_behavior
      @     requires positionExists(position);
      @     ensures \result == pieces[position.getRow()][position.getColumn()];
      @     assignable \nothing;
      @ also
      @ public exceptional_behavior
      @     requires !positionExists(position);
      @     signals_only RuntimeException;
      @     assignable \nothing;
      @*/
    public /*@ nullable */ Piece piece(Position position) {

        if (!positionExists(position)) {
            //@ assert position.getRow() < 0 || position.getRow() >= rows || position.getColumn() < 0 || position.getColumn() >= columns;
            throw new BoardException("A posição está fora do tabuleiro.");
        }

        return pieces[position.getRow()][position.getColumn()];
    }


    /*@ public normal_behavior
      @     requires positionExists(position);
      @     requires pieces[position.getRow()][position.getColumn()] == null;
      @     ensures pieces[position.getRow()][position.getColumn()] == piece;
      @     ensures piece.position == position;
      @     assignable pieces[position.getRow()][position.getColumn()], piece.position;
      @ also
      @ public exceptional_behavior
      @     requires !positionExists(position) || (pieces[position.getRow()][position.getColumn()] != null);
      @     signals_only RuntimeException;
      @     assignable \nothing;
      @*/
    public void placePiece(Piece piece, Position position){
        if(thereIsAPiece(position)){
            throw new BoardException("Já existe uma peça na posição "+ position);
        }

        pieces[position.getRow()][position.getColumn()] = piece;
        piece.position = position;

    }

    /*@ public normal_behavior
      @     requires positionExists(position) && pieces[position.getRow()][position.getColumn()] != null;
      @     ensures \result == (\old(pieces[position.getRow()][position.getColumn()]));
      @     ensures pieces[position.getRow()][position.getColumn()] == null;
      @     assignable pieces[position.getRow()][position.getColumn()], pieces[position.getRow()][position.getColumn()].position;
      @ also
      @ public normal_behavior
      @     requires positionExists(position) && pieces[position.getRow()][position.getColumn()] == null;
      @     ensures \result == null;
      @     assignable \nothing;
      @ also
      @ public exceptional_behavior
      @     requires !positionExists(position);
      @     signals_only RuntimeException;
      @     assignable \nothing;
      @*/
    public /*@ nullable */ Piece removePiece (Position position){
        if(!positionExists(position)){
            throw new BoardException("A posição fora do tabuleiro");
        }
        if (piece(position) == null) {
            return null;
        }
        Piece aux = piece(position);
        aux.position = null;

        pieces[position.getRow()][position.getColumn()] = null;
        return aux;
    }

    /*@ private normal_behavior
      @     requires row >= 0 && row < rows;
      @     requires column >= 0 && column < columns;
      @     ensures \result == true;
      @ also
      @ private normal_behavior
      @     requires row < 0 || row >= rows || column < 0 || column >= columns;
      @     ensures \result == false;
      @ spec_public
      @ pure helper
      @*/
    private boolean positionExistsBasic(int row, int column) {
        return row >= 0 && row < rows && column >= 0 && column < columns;
    }

    /*@ public normal_behavior
      @     requires position != null;
      @     ensures \result == (position.getRow() >= 0 && position.getRow() < this.rows
      @                    && position.getColumn() >= 0 && position.getColumn() < this.columns);
      @ pure
      @*/
    public boolean positionExists(Position position) {
        int row = position.getRow();
        int column = position.getColumn();
        return positionExistsBasic(row, column);
    }


    /*@ public normal_behavior
      @     requires positionExists(position);
      @     requires pieces[position.getRow()][position.getColumn()] != null;
      @     ensures \result == true;
      @     assignable \nothing;
      @ also
      @ public normal_behavior
      @     requires positionExists(position);
      @     requires pieces[position.getRow()][position.getColumn()] == null;
      @     ensures \result == false;
      @     assignable \nothing;
      @ also
      @ public exceptional_behavior
      @     requires !positionExists(position);
      @     signals_only RuntimeException;
      @     assignable \nothing;
      @*/
    public boolean thereIsAPiece(Position position) {

        if (!positionExists(position)) {
            throw new BoardException("A posição fora do tabuleiro");
        }
        return piece(position) != null;
    }
}
