package model.carrelloService;

import model.ConPool;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.mockito.MockedStatic;
import org.mockito.MockedConstruction;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

class RigaCarrelloDAOTest {

    private RigaCarrelloDAO rigaCarrelloDAO;
    private Connection mockConnection;
    private PreparedStatement mockPreparedStatement;
    private ResultSet mockResultSet;

    @BeforeEach
    void setUp() {
        rigaCarrelloDAO = new RigaCarrelloDAO();
        mockConnection = mock(Connection.class);
        mockPreparedStatement = mock(PreparedStatement.class);
        mockResultSet = mock(ResultSet.class);
    }

    // ==================== Tests for doRetrieveByIdCarrello ====================

    @Test
    @Timeout(value = 2, unit = TimeUnit.SECONDS)
    void testDoRetrieveByIdCarrello_MultipleRows() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class);
             MockedConstruction<LibroDAO> mockedLibroDAO = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    Libro libro = new Libro();
                    libro.setIsbn("978-3-16-148410-0");
                    libro.setTitolo("Test Book");
                    when(mock.doRetrieveById(anyString())).thenReturn(libro);
                })) {

            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);

            when(mockResultSet.next())
                    .thenReturn(true)
                    .thenReturn(true)
                    .thenReturn(false);
            when(mockResultSet.getString(1))
                    .thenReturn("CARR001")
                    .thenReturn("CARR001");
            when(mockResultSet.getString(2))
                    .thenReturn("978-3-16-148410-0")
                    .thenReturn("978-3-16-148410-1");
            when(mockResultSet.getInt(3))
                    .thenReturn(2)
                    .thenReturn(3);

            List<RigaCarrello> result = rigaCarrelloDAO.doRetrieveByIdCarrello("CARR001");

            assertNotNull(result);
            assertEquals(2, result.size());
            assertEquals("CARR001", result.get(0).getIdCarrello());
            assertEquals(2, result.get(0).getQuantita());
            assertEquals("CARR001", result.get(1).getIdCarrello());
            assertEquals(3, result.get(1).getQuantita());
            // Verify that libro is set properly - kills survived mutation on line 38
            assertNotNull(result.get(0).getLibro(), "Libro should be set for first item");
            assertNotNull(result.get(1).getLibro(), "Libro should be set for second item");
            verify(mockPreparedStatement).setString(1, "CARR001");
        }
    }
    
    @Test
    @Timeout(value = 2, unit = TimeUnit.SECONDS)
    void testDoRetrieveByIdCarrello_VerifyLibroNotNull() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class);
             MockedConstruction<LibroDAO> mockedLibroDAO = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    Libro libro = new Libro();
                    libro.setIsbn("978-3-16-148410-0");
                    libro.setTitolo("Test Book");
                    when(mock.doRetrieveById(anyString())).thenReturn(libro);
                })) {

            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);

            when(mockResultSet.next()).thenReturn(true).thenReturn(false);
            when(mockResultSet.getString(1)).thenReturn("CARR001");
            when(mockResultSet.getString(2)).thenReturn("978-3-16-148410-0");
            when(mockResultSet.getInt(3)).thenReturn(2);

            List<RigaCarrello> result = rigaCarrelloDAO.doRetrieveByIdCarrello("CARR001");

            assertNotNull(result);
            assertEquals(1, result.size());
            // This assertion will fail if setLibro is removed - kills survived mutation
            assertNotNull(result.get(0).getLibro(), "Libro must be set on RigaCarrello");
            assertEquals("978-3-16-148410-0", result.get(0).getLibro().getIsbn());
        }
    }

    @Test
    @Timeout(value = 2, unit = TimeUnit.SECONDS)
    void testDoRetrieveByIdCarrello_Empty() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
            when(mockResultSet.next()).thenReturn(false);

            List<RigaCarrello> result = rigaCarrelloDAO.doRetrieveByIdCarrello("CARR_EMPTY");

            assertNotNull(result);
            assertTrue(result.isEmpty());
            verify(mockPreparedStatement).setString(1, "CARR_EMPTY");
        }
    }

    @Test
    void testDoRetrieveByIdCarrello_SQLExceptionThrown() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Query error"));

            assertThrows(RuntimeException.class, () -> rigaCarrelloDAO.doRetrieveByIdCarrello("CARR001"));
        }
    }

    // ==================== Tests for doRetriveById ====================

    @Test
    void testDoRetriveById_Success() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class);
             MockedConstruction<LibroDAO> mockedLibroDAO = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    Libro libro = new Libro();
                    libro.setIsbn("978-3-16-148410-0");
                    libro.setTitolo("Test Book");
                    when(mock.doRetrieveById(anyString())).thenReturn(libro);
                })) {

            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);

            when(mockResultSet.next()).thenReturn(true);
            when(mockResultSet.getString(1)).thenReturn("CARR001");
            when(mockResultSet.getString(2)).thenReturn("978-3-16-148410-0");
            when(mockResultSet.getInt(3)).thenReturn(5);

            RigaCarrello result = rigaCarrelloDAO.doRetriveById("CARR001", "978-3-16-148410-0");

            assertNotNull(result);
            assertEquals("CARR001", result.getIdCarrello());
            assertEquals(5, result.getQuantita());
            assertNotNull(result.getLibro());
            verify(mockPreparedStatement).setString(1, "CARR001");
            verify(mockPreparedStatement).setString(2, "978-3-16-148410-0");
        }
    }

    @Test
    void testDoRetriveById_NotFound() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
            when(mockResultSet.next()).thenReturn(false);

            RigaCarrello result = rigaCarrelloDAO.doRetriveById("CARR_NONEXISTENT", "ISBN_NONEXISTENT");

            assertNull(result);
            verify(mockPreparedStatement).setString(1, "CARR_NONEXISTENT");
            verify(mockPreparedStatement).setString(2, "ISBN_NONEXISTENT");
        }
    }

    @Test
    void testDoRetriveById_SQLExceptionThrown() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("DB error"));

            assertThrows(RuntimeException.class, () -> rigaCarrelloDAO.doRetriveById("CARR001", "ISBN"));
        }
    }

    // ==================== Tests for doSave ====================

    @Test
    void testDoSave_Success() throws SQLException {
        Libro libro = new Libro();
        libro.setIsbn("978-3-16-148410-0");

        RigaCarrello rigaCarrello = new RigaCarrello();
        rigaCarrello.setIdCarrello("CARR001");
        rigaCarrello.setLibro(libro);
        rigaCarrello.setQuantita(10);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> rigaCarrelloDAO.doSave(rigaCarrello));

            verify(mockConnection).prepareStatement("INSERT INTO RigaCarrello (idCarrello, isbn, quantita) VALUES(?,?,?)");
            verify(mockPreparedStatement).setString(1, "CARR001");
            verify(mockPreparedStatement).setString(2, "978-3-16-148410-0");
            verify(mockPreparedStatement).setInt(3, 10);
        }
    }

    @Test
    void testDoSave_InsertError() throws SQLException {
        Libro libro = new Libro();
        libro.setIsbn("978-3-16-148410-0");

        RigaCarrello rigaCarrello = new RigaCarrello();
        rigaCarrello.setIdCarrello("CARR002");
        rigaCarrello.setLibro(libro);
        rigaCarrello.setQuantita(5);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(0);

            RuntimeException exception = assertThrows(RuntimeException.class, () -> rigaCarrelloDAO.doSave(rigaCarrello));
            assertEquals("INSERT error.", exception.getMessage());
        }
    }

    @Test
    void testDoSave_SQLExceptionThrown() throws SQLException {
        Libro libro = new Libro();
        libro.setIsbn("978-3-16-148410-0");

        RigaCarrello rigaCarrello = new RigaCarrello();
        rigaCarrello.setIdCarrello("CARR003");
        rigaCarrello.setLibro(libro);
        rigaCarrello.setQuantita(3);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Connection error"));

            assertThrows(RuntimeException.class, () -> rigaCarrelloDAO.doSave(rigaCarrello));
        }
    }

    // ==================== Tests for deleteRigaCarrello ====================

    @Test
    void testDeleteRigaCarrello_Success() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> rigaCarrelloDAO.deleteRigaCarrello("978-3-16-148410-0", "CARR001"));

            verify(mockConnection).prepareStatement("DELETE FROM RigaCarrello WHERE idCarrello=? AND isbn =?");
            verify(mockPreparedStatement).setString(1, "CARR001");
            verify(mockPreparedStatement).setString(2, "978-3-16-148410-0");
        }
    }

    @Test
    void testDeleteRigaCarrello_NoRowsDeleted() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(0);

            RuntimeException exception = assertThrows(RuntimeException.class, 
                () -> rigaCarrelloDAO.deleteRigaCarrello("ISBN", "CARR_NONEXISTENT"));
            assertEquals("DELETE error.", exception.getMessage());
        }
    }

    @Test
    void testDeleteRigaCarrello_SQLExceptionThrown() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("DB error"));

            assertThrows(RuntimeException.class, () -> rigaCarrelloDAO.deleteRigaCarrello("ISBN", "CARR001"));
        }
    }

    // ==================== Tests for deleteRigheCarrelloByIdCarrello ====================

    @Test
    void testDeleteRigheCarrelloByIdCarrello_Success() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(5); // Multiple rows deleted

            assertDoesNotThrow(() -> rigaCarrelloDAO.deleteRigheCarrelloByIdCarrello("CARR001"));

            verify(mockConnection).prepareStatement("DELETE FROM RigaCarrello WHERE idCarrello=?");
            verify(mockPreparedStatement).setString(1, "CARR001");
        }
    }
    
    @Test
    void testDeleteRigheCarrelloByIdCarrello_ExactlyOneRowDeleted() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            // Return exactly 1 to test boundary condition (< 1 should throw, >= 1 should not)
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            // This should succeed when 1 row is deleted - kills boundary mutation
            assertDoesNotThrow(() -> rigaCarrelloDAO.deleteRigheCarrelloByIdCarrello("CARR002"));

            verify(mockPreparedStatement).setString(1, "CARR002");
        }
    }

    @Test
    void testDeleteRigheCarrelloByIdCarrello_NoRowsDeleted() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(0);

            RuntimeException exception = assertThrows(RuntimeException.class,
                () -> rigaCarrelloDAO.deleteRigheCarrelloByIdCarrello("CARR_EMPTY"));
            assertEquals("UPDATE error.", exception.getMessage());
        }
    }

    @Test
    void testDeleteRigheCarrelloByIdCarrello_SQLExceptionThrown() throws SQLException {
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Connection failed"));

            assertThrows(RuntimeException.class, () -> rigaCarrelloDAO.deleteRigheCarrelloByIdCarrello("CARR001"));
        }
    }

    // ==================== Tests for updateQuantita ====================

    @Test
    void testUpdateQuantita_Success() throws SQLException {
        Libro libro = new Libro();
        libro.setIsbn("978-3-16-148410-0");

        RigaCarrello rigaCarrello = new RigaCarrello();
        rigaCarrello.setIdCarrello("CARR001");
        rigaCarrello.setLibro(libro);
        rigaCarrello.setQuantita(15);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> rigaCarrelloDAO.updateQuantita(rigaCarrello));

            verify(mockConnection).prepareStatement("UPDATE RigaCarrello SET quantita = ? WHERE isbn = ? AND idCarrello=?");
            verify(mockPreparedStatement).setInt(1, 15);
            verify(mockPreparedStatement).setString(2, "978-3-16-148410-0");
            verify(mockPreparedStatement).setString(3, "CARR001");
        }
    }

    @Test
    void testUpdateQuantita_NoRowsUpdated() throws SQLException {
        Libro libro = new Libro();
        libro.setIsbn("ISBN_NONEXISTENT");

        RigaCarrello rigaCarrello = new RigaCarrello();
        rigaCarrello.setIdCarrello("CARR_NONEXISTENT");
        rigaCarrello.setLibro(libro);
        rigaCarrello.setQuantita(20);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(0);

            RuntimeException exception = assertThrows(RuntimeException.class, () -> rigaCarrelloDAO.updateQuantita(rigaCarrello));
            assertEquals("UPDATE error.", exception.getMessage());
        }
    }

    @Test
    void testUpdateQuantita_SQLExceptionThrown() throws SQLException {
        Libro libro = new Libro();
        libro.setIsbn("978-3-16-148410-0");

        RigaCarrello rigaCarrello = new RigaCarrello();
        rigaCarrello.setIdCarrello("CARR001");
        rigaCarrello.setLibro(libro);
        rigaCarrello.setQuantita(10);

        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("Update failed"));

            assertThrows(RuntimeException.class, () -> rigaCarrelloDAO.updateQuantita(rigaCarrello));
        }
    }

    // ==================== Integration and Edge Case Tests ====================

    @Test
    void testFullRigaCarrelloLifecycle() throws SQLException {
        Libro libro = new Libro();
        libro.setIsbn("978-3-16-148410-0");

        RigaCarrello rigaCarrello = new RigaCarrello();
        rigaCarrello.setIdCarrello("CARR_LIFECYCLE");
        rigaCarrello.setLibro(libro);
        rigaCarrello.setQuantita(5);

        // Test save
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> rigaCarrelloDAO.doSave(rigaCarrello));
        }

        // Test update
        rigaCarrello.setQuantita(10);
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> rigaCarrelloDAO.updateQuantita(rigaCarrello));
        }

        // Test delete
        try (MockedStatic<ConPool> mockedConPool = mockStatic(ConPool.class)) {
            mockedConPool.when(ConPool::getConnection).thenReturn(mockConnection);
            when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
            when(mockPreparedStatement.executeUpdate()).thenReturn(1);

            assertDoesNotThrow(() -> rigaCarrelloDAO.deleteRigaCarrello("978-3-16-148410-0", "CARR_LIFECYCLE"));
        }
    }
}
