package model.libroService;

import model.ConPool;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;
import org.mockito.MockedStatic;
import org.mockito.Mockito;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Test class for AutoreDAO
 * Tests all CRUD operations and author management methods
 */
class AutoreDAOTest {

    private AutoreDAO autoreDAO;
    private Connection mockConnection;
    private PreparedStatement mockPreparedStatement;
    private ResultSet mockResultSet;
    private MockedStatic<ConPool> mockedConPool;

    @BeforeEach
    void setUp() throws SQLException {
        mockConnection = mock(Connection.class);
        mockPreparedStatement = mock(PreparedStatement.class);
        mockResultSet = mock(ResultSet.class);
        
        autoreDAO = new AutoreDAO();
        
        mockedConPool = mockStatic(ConPool.class);
        mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
    }

    @AfterEach
    void tearDown() {
        if (mockedConPool != null) {
            mockedConPool.close();
        }
    }

    // ==================== Helper Methods ====================

    private Autore createTestAutore(String cf, String nome, String cognome) {
        Autore autore = new Autore();
        autore.setCf(cf);
        autore.setNome(nome);
        autore.setCognome(cognome);
        return autore;
    }

    // ==================== doSave Tests ====================

    @Test
    void testDoSave_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString(), anyInt())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        Autore a = createTestAutore("CF123", "Mario", "Rossi");

        // Act
        assertDoesNotThrow(() -> autoreDAO.doSave(a));

        // Assert
        verify(mockPreparedStatement).setString(1, "CF123");
        verify(mockPreparedStatement).setString(2, "Mario");
        verify(mockPreparedStatement).setString(3, "Rossi");
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDoSave_InsertFails() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString(), anyInt())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        Autore a = createTestAutore("CFERR", "Nome", "Cognome");

        // Act & Assert
        assertThrows(RuntimeException.class, () -> autoreDAO.doSave(a));
    }

    @Test
    void testDoSave_SQLExceptionThrown() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString(), anyInt())).thenThrow(new SQLException("fail"));

        Autore a = createTestAutore("CFSQL", "N", "C");

        // Act & Assert
        assertThrows(RuntimeException.class, () -> autoreDAO.doSave(a));
    }

    // ==================== deleteAutore Tests ====================

    @Test
    void testDeleteAutore_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        // Act
        assertDoesNotThrow(() -> autoreDAO.deleteAutore("CFDEL"));

        // Assert
        verify(mockPreparedStatement).setString(1, "CFDEL");
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDeleteAutore_DeleteFails() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> autoreDAO.deleteAutore("CFDELERR"));
    }

    @Test
    void testDeleteAutore_SQLExceptionThrown() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("delete error"));

        // Act & Assert
        assertThrows(RuntimeException.class, () -> autoreDAO.deleteAutore("CFSQL"));
    }

    // ==================== searchAutore Tests ====================

    @Test
    void testSearchAutore_Found() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getString(1)).thenReturn("Luca");
        when(mockResultSet.getString(2)).thenReturn("Bianchi");

        // Act
        Autore a = autoreDAO.searchAutore("CFSRCH");

        // Assert
        assertNotNull(a);
        assertEquals("CFSRCH", a.getCf());
        assertEquals("Luca", a.getNome());
        assertEquals("Bianchi", a.getCognome());
    }

    @Test
    void testSearchAutore_NotFound() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        Autore a = autoreDAO.searchAutore("CFNOT");

        // Assert
        assertNull(a);
    }

    @Test
    void testSearchAutore_SQLExceptionThrown() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("search error"));

        // Act & Assert
        assertThrows(RuntimeException.class, () -> autoreDAO.searchAutore("CFSQL"));
    }

    @Test
    void testSearchAutore_ResultSetThrowsSQLException() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getString(1)).thenThrow(new SQLException("ResultSet error"));

        // Act & Assert
        assertThrows(RuntimeException.class, () -> autoreDAO.searchAutore("CFRS_ERROR"));
    }

    @Test
    void testSearchAutore_ExecuteQueryThrowsSQLException() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenThrow(new SQLException("executeQuery error"));

        // Act & Assert
        assertThrows(RuntimeException.class, () -> autoreDAO.searchAutore("CFEXEC"));
    }

    @Test
    void testSearchAutore_VerifySetStringCalled() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        autoreDAO.searchAutore("CF_VERIFY");

        // Assert - verify setString was called with the correct cf parameter
        verify(mockPreparedStatement).setString(1, "CF_VERIFY");
    }

    // ==================== getScrittura Tests ====================

    @Test
    void testGetScrittura_ReturnsList() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, true, false);
        when(mockResultSet.getString(1)).thenReturn("ISBN1", "ISBN2");

        Libro l1 = new Libro();
        l1.setIsbn("ISBN1");
        Libro l2 = new Libro();
        l2.setIsbn("ISBN2");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById("ISBN1")).thenReturn(l1);
                    when(mock.doRetrieveById("ISBN2")).thenReturn(l2);
                })) {

            // Act
            List<Libro> list = autoreDAO.getScrittura("CFSCR");

            // Assert
            assertNotNull(list);
            assertEquals(2, list.size());
            assertEquals("ISBN1", list.get(0).getIsbn());
            assertEquals("ISBN2", list.get(1).getIsbn());
        }
    }

    @Test
    void testGetScrittura_Empty_ReturnsEmptyList() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        List<Libro> list = autoreDAO.getScrittura("CFSCR_EMPTY");

        // Assert
        assertNotNull(list);
        assertEquals(0, list.size());
    }

    @Test
    void testGetScrittura_LibroDAOReturnsNull_ListContainsNull() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, false);
        when(mockResultSet.getString(1)).thenReturn("ISBN_NULL");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById("ISBN_NULL")).thenReturn(null);
                })) {

            // Act
            List<Libro> list = autoreDAO.getScrittura("CFSCR_NULL");

            // Assert
            assertNotNull(list);
            assertEquals(1, list.size());
            assertNull(list.get(0));
        }
    }

    @Test
    void testGetScrittura_SQLExceptionThrown() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("getScrittura error"));

        // Act & Assert
        assertThrows(RuntimeException.class, () -> autoreDAO.getScrittura("CFSQL"));
    }

    @Test
    void testGetScrittura_VerifySetStringCalled() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        autoreDAO.getScrittura("CF_VERIFY_SCRITTURA");

        // Assert - verify setString was called with the correct cf parameter
        verify(mockPreparedStatement).setString(1, "CF_VERIFY_SCRITTURA");
    }

    @Test
    void testGetScrittura_VerifyLoopTerminates() throws SQLException {
        // Arrange - setup to verify the while loop correctly terminates
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        // Return true exactly 3 times, then false to terminate
        when(mockResultSet.next()).thenReturn(true, true, true, false);
        when(mockResultSet.getString(1)).thenReturn("ISBN1", "ISBN2", "ISBN3");

        Libro l1 = new Libro();
        l1.setIsbn("ISBN1");
        Libro l2 = new Libro();
        l2.setIsbn("ISBN2");
        Libro l3 = new Libro();
        l3.setIsbn("ISBN3");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById("ISBN1")).thenReturn(l1);
                    when(mock.doRetrieveById("ISBN2")).thenReturn(l2);
                    when(mock.doRetrieveById("ISBN3")).thenReturn(l3);
                })) {

            // Act
            List<Libro> list = autoreDAO.getScrittura("CFLOOP");

            // Assert - verify exactly 3 items processed (loop terminated correctly)
            assertNotNull(list);
            assertEquals(3, list.size());
            // Verify rs.next() was called exactly 4 times (3 true, 1 false)
            verify(mockResultSet, times(4)).next();
        }
    }

}