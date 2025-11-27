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
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Test class for RepartoDAO
 * Tests all CRUD operations and reparto management methods
 */
class RepartoDAOTest {

    private RepartoDAO repartoDAO;
    private Connection mockConnection;
    private PreparedStatement mockPreparedStatement;
    private ResultSet mockResultSet;
    private MockedStatic<ConPool> mockedConPool;

    @BeforeEach
    void setUp() throws SQLException {
        mockConnection = mock(Connection.class);
        mockPreparedStatement = mock(PreparedStatement.class);
        mockResultSet = mock(ResultSet.class);
        
        repartoDAO = new RepartoDAO();
        
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

    private Reparto createTestReparto(int idReparto, String nome, String descrizione, String immagine) {
        Reparto reparto = new Reparto();
        reparto.setIdReparto(idReparto);
        reparto.setNome(nome);
        reparto.setDescrizione(descrizione);
        reparto.setImmagine(immagine);
        return reparto;
    }

    // ==================== doRetrieveById Tests ====================

    @Test
    void testDoRetrieveById_Found() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt(1)).thenReturn(7);
        when(mockResultSet.getString(2)).thenReturn("NomeR");
        when(mockResultSet.getString(3)).thenReturn("Desc");
        when(mockResultSet.getString(4)).thenReturn("img.png");

        RepartoDAO spy = spy(repartoDAO);
        doReturn(Collections.emptyList()).when(spy).getAppartenenza(7);

        // Act
        Reparto r = spy.doRetrieveById(7);

        // Assert
        assertNotNull(r);
        assertEquals(7, r.getIdReparto());
        assertEquals("NomeR", r.getNome());
        assertEquals("Desc", r.getDescrizione());
        assertEquals(0, r.getLibri().size());
    }

    @Test
    void testDoRetrieveById_NotFound() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        Reparto r = repartoDAO.doRetrieveById(999);

        // Assert
        assertNull(r);
    }

    @Test
    void testDoRetrieveById_SQLExceptionThrown() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("retrieve error"));

        // Act & Assert
        assertThrows(RuntimeException.class, () -> repartoDAO.doRetrieveById(1));
    }

    @Test
    void testDoRetrieveById_VerifySetIntAndSetImageCalled() throws SQLException {
        // Arrange - This test kills mutations on lines 168 and 175
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt(1)).thenReturn(999);
        when(mockResultSet.getString(2)).thenReturn("NomeTest");
        when(mockResultSet.getString(3)).thenReturn("DescTest");
        when(mockResultSet.getString(4)).thenReturn("imageTest.png");

        RepartoDAO spy = spy(repartoDAO);
        doReturn(Collections.emptyList()).when(spy).getAppartenenza(999);

        // Act
        Reparto r = spy.doRetrieveById(999);

        // Assert - Verify setInt was called on PreparedStatement
        verify(mockPreparedStatement).setInt(1, 999);
        
        // Assert - Verify all properties including immagine are set correctly
        assertNotNull(r);
        assertEquals(999, r.getIdReparto());
        assertEquals("NomeTest", r.getNome());
        assertEquals("DescTest", r.getDescrizione());
        assertEquals("imageTest.png", r.getImmagine());
        assertNotNull(r.getLibri());
    }

    // ==================== getAppartenenza Tests ====================

    @Test
    void testDoRetrivedAll_ReturnsList() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, true, false);
        when(mockResultSet.getInt(1)).thenReturn(1, 2);
        when(mockResultSet.getString(2)).thenReturn("R1", "R2");
        when(mockResultSet.getString(3)).thenReturn("D1", "D2");
        when(mockResultSet.getString(4)).thenReturn("i1.png", "i2.png");

        RepartoDAO spy = spy(repartoDAO);
        doReturn(Collections.emptyList()).when(spy).getAppartenenza(anyInt());

        // Act
        List<Reparto> list = spy.doRetrivedAll();

        // Assert
        assertNotNull(list);
        assertEquals(2, list.size());
        assertEquals(1, list.get(0).getIdReparto());
        assertEquals(2, list.get(1).getIdReparto());
    }

    @Test
    void testDoRetrivedAll_SQLExceptionThrown() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("retriveAll error"));

        // Act & Assert
        assertThrows(RuntimeException.class, () -> repartoDAO.doRetrivedAll());
    }

    @Test
    void testDoRetrivedAll_VerifyAllSettersCalled() throws SQLException {
        // Arrange - This test kills mutations on lines 145-148
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, false);
        when(mockResultSet.getInt(1)).thenReturn(100);
        when(mockResultSet.getString(2)).thenReturn("RepartoNome");
        when(mockResultSet.getString(3)).thenReturn("RepartoDescrizione");
        when(mockResultSet.getString(4)).thenReturn("immagine.png");

        List<Libro> testLibri = new ArrayList<>();
        testLibri.add(new Libro());

        RepartoDAO spy = spy(repartoDAO);
        doReturn(testLibri).when(spy).getAppartenenza(100);

        // Act
        List<Reparto> result = spy.doRetrivedAll();

        // Assert - Verify all setters were called and values are correct
        assertNotNull(result);
        assertEquals(1, result.size());
        Reparto r = result.get(0);
        assertEquals(100, r.getIdReparto());
        assertEquals("RepartoNome", r.getNome());
        assertEquals("RepartoDescrizione", r.getDescrizione());
        assertEquals("immagine.png", r.getImmagine());
        assertNotNull(r.getLibri());
        assertEquals(1, r.getLibri().size());
    }

    // ==================== doRetrieveById Tests ====================

    @Test
    void testDoSave_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString(), anyInt())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);
        when(mockPreparedStatement.getGeneratedKeys()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt(1)).thenReturn(123);

        Reparto r = createTestReparto(0, "N", "D", null);

        // Act
        repartoDAO.doSave(r);

        // Assert
        assertEquals(123, r.getIdReparto());
    }

    @Test
    void testDoSave_InsertFails() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("INSERT INTO Reparto"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        Reparto r = createTestReparto(0, "N", "D", null);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> repartoDAO.doSave(r));
    }

    @Test
    void testDoSave_NoGeneratedKeys() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString(), anyInt())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);
        when(mockPreparedStatement.getGeneratedKeys()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        Reparto r = createTestReparto(0, "N", "D", null);

        // Act
        repartoDAO.doSave(r);

        // Assert
        assertEquals(0, r.getIdReparto());
    }

    @Test
    void testDoSave_SQLExceptionThrown() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString(), anyInt())).thenThrow(new SQLException("save error"));

        Reparto r = createTestReparto(0, "N", "D", null);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> repartoDAO.doSave(r));
    }

    @Test
    void testDoSave_GetGeneratedKeysThrowsSQLException() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString(), anyInt())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);
        when(mockPreparedStatement.getGeneratedKeys()).thenThrow(new SQLException("keys error"));

        Reparto r = createTestReparto(0, "N", "D", null);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> repartoDAO.doSave(r));
    }

    @Test
    void testDoSave_VerifySetStringCalls() throws SQLException {
        // Arrange - This test kills mutations on lines 21-23
        when(mockConnection.prepareStatement(anyString(), anyInt())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);
        when(mockPreparedStatement.getGeneratedKeys()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt(1)).thenReturn(555);

        Reparto r = createTestReparto(0, "TestNome", "TestDesc", "TestImg.jpg");

        // Act
        repartoDAO.doSave(r);

        // Assert - Verify all setString calls are made
        verify(mockPreparedStatement).setString(1, "TestNome");
        verify(mockPreparedStatement).setString(2, "TestDesc");
        verify(mockPreparedStatement).setString(3, "TestImg.jpg");
        assertEquals(555, r.getIdReparto());
    }

    // ==================== updateReparto Tests ====================

    @Test
    void testUpdateReparto_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("UPDATE Reparto SET"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        Reparto r = createTestReparto(5, "Name", "NEWDES", "imgx.png");

        // Act
        assertDoesNotThrow(() -> repartoDAO.updateReparto(r));

        // Assert
        verify(mockPreparedStatement).setString(1, "NEWDES");
        verify(mockPreparedStatement).setString(2, "imgx.png");
        verify(mockPreparedStatement).setInt(3, 5);
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testUpdateReparto_NoRowsUpdated() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("UPDATE Reparto SET"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        Reparto r = createTestReparto(5, "N", "D", "i.png");

        // Act & Assert
        assertThrows(RuntimeException.class, () -> repartoDAO.updateReparto(r));
    }

    @Test
    void testUpdateReparto_SQLExceptionThrown() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("UPDATE Reparto SET"))).thenThrow(new SQLException("update error"));

        Reparto r = createTestReparto(5, "N", "D", "i.png");

        // Act & Assert
        assertThrows(RuntimeException.class, () -> repartoDAO.updateReparto(r));
    }

    // ==================== deleteReparto Tests ====================

    @Test
    void testDeleteReparto_WithAppartenenza_Success() throws SQLException {
        // Arrange
        PreparedStatement ps1 = mock(PreparedStatement.class);
        PreparedStatement ps2 = mock(PreparedStatement.class);

        when(mockConnection.prepareStatement(anyString())).thenReturn(ps1, ps2);
        when(ps1.executeUpdate()).thenReturn(1);
        when(ps2.executeUpdate()).thenReturn(1);

        Reparto reparto = new Reparto();
        reparto.setIdReparto(7);
        List<Libro> libri = new ArrayList<>();
        libri.add(new Libro());

        RepartoDAO spyDao = spy(repartoDAO);
        doReturn(libri).when(spyDao).getAppartenenza(7);
        doReturn(reparto).when(spyDao).doRetrieveById(7);

        // Act
        assertDoesNotThrow(() -> spyDao.deleteReparto(7));

        // Assert
        verify(ps1).setInt(1, 7);
        verify(ps1).executeUpdate();
        verify(ps2).setInt(1, 7);
        verify(ps2).executeUpdate();
    }

    @Test
    void testDeleteReparto_NoAppartenenza_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        RepartoDAO spyDao = spy(repartoDAO);
        doReturn(Collections.emptyList()).when(spyDao).getAppartenenza(anyInt());
        doReturn(new Reparto()).when(spyDao).doRetrieveById(anyInt());

        // Act
        assertDoesNotThrow(() -> spyDao.deleteReparto(11));

        // Assert
        verify(mockPreparedStatement, atLeastOnce()).executeUpdate();
    }

    @Test
    void testDeleteReparto_AppartenenzaExecuteFails() throws SQLException {
        // Arrange
        PreparedStatement psApp = mock(PreparedStatement.class);
        PreparedStatement psRep = mock(PreparedStatement.class);

        when(mockConnection.prepareStatement(anyString())).thenReturn(psApp, psRep);
        when(psApp.executeUpdate()).thenReturn(0);
        when(psRep.executeUpdate()).thenReturn(1);

        Reparto reparto = new Reparto();
        reparto.setIdReparto(7);
        List<Libro> libri = new ArrayList<>();
        libri.add(new Libro());

        RepartoDAO spyDao = spy(repartoDAO);
        doReturn(libri).when(spyDao).getAppartenenza(7);
        doReturn(reparto).when(spyDao).doRetrieveById(7);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> spyDao.deleteReparto(7));
    }

    @Test
    void testDeleteReparto_GetAppartenenzaNull_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        RepartoDAO spyDao = spy(repartoDAO);
        doReturn(null).when(spyDao).getAppartenenza(anyInt());
        doReturn(new Reparto()).when(spyDao).doRetrieveById(anyInt());

        // Act
        assertDoesNotThrow(() -> spyDao.deleteReparto(13));

        // Assert
        verify(mockPreparedStatement).setInt(1, 13);
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDeleteReparto_RepartoDeleteFails() throws SQLException {
        // Arrange
        PreparedStatement psApp = mock(PreparedStatement.class);
        PreparedStatement psRep = mock(PreparedStatement.class);

        when(mockConnection.prepareStatement(anyString())).thenReturn(psApp, psRep);
        when(psApp.executeUpdate()).thenReturn(1);
        when(psRep.executeUpdate()).thenReturn(0);

        Reparto reparto = new Reparto();
        reparto.setIdReparto(22);
        List<Libro> libri = new ArrayList<>();
        libri.add(new Libro());

        RepartoDAO spyDao = spy(repartoDAO);
        doReturn(libri).when(spyDao).getAppartenenza(22);
        doReturn(reparto).when(spyDao).doRetrieveById(22);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> spyDao.deleteReparto(22));
    }

    @Test
    void testDeleteReparto_SQLExceptionThrown() throws SQLException {
        // Arrange
        RepartoDAO spyDao = spy(repartoDAO);
        doThrow(new RuntimeException(new SQLException("delete error"))).when(spyDao).getAppartenenza(anyInt());

        // Act & Assert
        assertThrows(RuntimeException.class, () -> spyDao.deleteReparto(5));
    }

    @Test
    void testDeleteReparto_VerifySetLibriCall() throws SQLException {
        // Arrange - This test kills mutation on line 51
        PreparedStatement ps1 = mock(PreparedStatement.class);
        PreparedStatement ps2 = mock(PreparedStatement.class);

        when(mockConnection.prepareStatement(anyString())).thenReturn(ps1, ps2);
        when(ps1.executeUpdate()).thenReturn(1);
        when(ps2.executeUpdate()).thenReturn(1);

        Reparto reparto = spy(new Reparto());
        reparto.setIdReparto(7);
        List<Libro> libri = new ArrayList<>();
        libri.add(new Libro());
        reparto.setLibri(libri);

        RepartoDAO spyDao = spy(repartoDAO);
        doReturn(libri).when(spyDao).getAppartenenza(7);
        doReturn(reparto).when(spyDao).doRetrieveById(7);

        // Act
        spyDao.deleteReparto(7);

        // Assert - Verify setLibri(null) was called
        verify(reparto).setLibri(null);
    }

    // ==================== aggiungiLibroReparto Tests ====================

    @Test
    void testAggiungiLibroReparto_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        Reparto reparto = new Reparto();
        reparto.setIdReparto(10);
        reparto.setLibri(new ArrayList<>());

        Libro l = new Libro();
        l.setIsbn("ISBNX");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, ctx) -> when(mock.doRetrieveById("ISBNX")).thenReturn(l))) {

            // Act
            repartoDAO.aggiungiLibroReparto(reparto, "ISBNX");

            // Assert
            verify(mockPreparedStatement).setInt(1, 10);
            verify(mockPreparedStatement).setString(2, "ISBNX");
            verify(mockPreparedStatement).executeUpdate();

            assertEquals(1, reparto.getLibri().size());
            assertEquals("ISBNX", reparto.getLibri().get(0).getIsbn());
        }
    }

    @Test
    void testAggiungiLibroReparto_InsertFails() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        Reparto reparto = new Reparto();
        reparto.setIdReparto(20);
        reparto.setLibri(new ArrayList<>());

        // Act & Assert
        assertThrows(RuntimeException.class, () -> repartoDAO.aggiungiLibroReparto(reparto, "XISBN"));
    }

    @Test
    void testAggiungiLibroReparto_SQLExceptionThrown() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("aggiungi error"));

        Reparto reparto = new Reparto();
        reparto.setIdReparto(20);
        reparto.setLibri(new ArrayList<>());

        // Act & Assert
        assertThrows(RuntimeException.class, () -> repartoDAO.aggiungiLibroReparto(reparto, "XISBN"));
    }

    // ==================== removeLibroReparto Tests ====================

    @Test
    void testRemoveLibroReparto_ExecuteUpdateFails() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        Reparto reparto = new Reparto();
        reparto.setIdReparto(5);
        Libro l = new Libro();
        l.setIsbn("BISBN");
        reparto.setLibri(new ArrayList<>());
        reparto.getLibri().add(l);

        RepartoDAO spyDao = spy(repartoDAO);
        doReturn(reparto).when(spyDao).doRetrieveById(5);

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, ctx) -> when(mock.doRetrieveById("BISBN")).thenReturn(l))) {

            // Act & Assert
            assertThrows(RuntimeException.class, () -> spyDao.removeLibroReparto(5, "BISBN"));
        }
    }

    @Test
    void testRemoveLibroReparto_SQLExceptionThrown() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("remove error"));

        Reparto reparto = new Reparto();
        reparto.setIdReparto(5);

        RepartoDAO spyDao = spy(repartoDAO);
        doReturn(reparto).when(spyDao).doRetrieveById(5);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> spyDao.removeLibroReparto(5, "BISBN"));
    }

    @Test
    void testRemoveLibroReparto_VerifyPreparedStatementCalls() throws SQLException {
        // Arrange - This test kills mutations on lines 92-93
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        Reparto reparto = new Reparto();
        reparto.setIdReparto(42);
        Libro libro = new Libro();
        libro.setIsbn("TEST-ISBN-123");
        List<Libro> libri = new ArrayList<>();
        libri.add(libro);
        reparto.setLibri(libri);

        RepartoDAO spyDao = spy(repartoDAO);
        doReturn(reparto).when(spyDao).doRetrieveById(42);

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, ctx) -> when(mock.doRetrieveById("TEST-ISBN-123")).thenReturn(libro))) {

            // Act
            spyDao.removeLibroReparto(42, "TEST-ISBN-123");

            // Assert - Verify setInt and setString were called
            verify(mockPreparedStatement).setInt(1, 42);
            verify(mockPreparedStatement).setString(2, "TEST-ISBN-123");
            verify(mockPreparedStatement).executeUpdate();
            // Verify libro was removed from list
            assertEquals(0, reparto.getLibri().size());
        }
    }

    // ==================== doSaveAppartenenza Tests ====================

    @Test
    void testDoSaveAppartenenza_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("INSERT INTO Appartenenza"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        // Act
        assertDoesNotThrow(() -> repartoDAO.doSaveAppartenenza(2, "isbn-okay"));

        // Assert
        verify(mockPreparedStatement).setInt(1, 2);
        verify(mockPreparedStatement).setString(2, "isbn-okay");
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDoSaveAppartenenza_ExecuteUpdateFails() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("INSERT INTO Appartenenza"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> repartoDAO.doSaveAppartenenza(2, "isbn"));
    }

    // ==================== deleteFromAppartenenzaLibro Tests ====================

    @Test
    void testDeleteFromAppartenenzaLibro_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("DELETE FROM Appartenenza WHERE"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        // Act
        assertDoesNotThrow(() -> repartoDAO.deleteFromAppartenenzaLibro(3, "AAA"));

        // Assert
        verify(mockPreparedStatement).setInt(1, 3);
        verify(mockPreparedStatement).setString(2, "AAA");
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDeleteFromAppartenenzaLibro_ExecuteUpdateFails() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("DELETE FROM Appartenenza WHERE"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> repartoDAO.deleteFromAppartenenzaLibro(3, "AAA"));
    }

    @Test
    void testDeleteFromAppartenenzaLibro_SQLExceptionThrown() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("DELETE FROM Appartenenza WHERE"))).thenThrow(new SQLException("deleteFrom error"));

        // Act & Assert
        assertThrows(RuntimeException.class, () -> repartoDAO.deleteFromAppartenenzaLibro(3, "AAA"));
    }

    // ==================== getAppartenenza Tests ====================

    @Test
    void testGetAppartenenza_ReturnsList() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("Appartenenza"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, false);
        when(mockResultSet.getString(1)).thenReturn("ISBN-G1");

        Libro libro = new Libro();
        libro.setIsbn("ISBN-G1");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, ctx) -> when(mock.doRetrieveById("ISBN-G1")).thenReturn(libro))) {

            // Act
            List<Libro> list = repartoDAO.getAppartenenza(9);

            // Assert
            assertNotNull(list);
            assertEquals(1, list.size());
            assertEquals("ISBN-G1", list.get(0).getIsbn());
        }
    }

    @Test
    void testGetAppartenenza_EmptyList() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("Appartenenza"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        List<Libro> list = repartoDAO.getAppartenenza(9);

        // Assert
        assertNotNull(list);
        assertEquals(0, list.size());
    }

    @Test
    void testGetAppartenenza_SQLExceptionThrown() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("Appartenenza"))).thenThrow(new SQLException("getAppartenenza error"));

        // Act & Assert
        assertThrows(RuntimeException.class, () -> repartoDAO.getAppartenenza(9));
    }

    @Test
    void testGetAppartenenza_VerifySetIntCalled() throws SQLException {
        // Arrange - This test kills mutation on line 194
        when(mockConnection.prepareStatement(contains("Appartenenza"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, false);
        when(mockResultSet.getString(1)).thenReturn("ISBN-TEST-456");

        Libro libro = new Libro();
        libro.setIsbn("ISBN-TEST-456");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, ctx) -> when(mock.doRetrieveById("ISBN-TEST-456")).thenReturn(libro))) {

            // Act
            List<Libro> list = repartoDAO.getAppartenenza(777);

            // Assert - Verify setInt was called with correct value
            verify(mockPreparedStatement).setInt(1, 777);
            verify(mockPreparedStatement).executeQuery();
            
            // Verify result is correct
            assertNotNull(list);
            assertEquals(1, list.size());
            assertEquals("ISBN-TEST-456", list.get(0).getIsbn());
        }
    }
}
