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
 * Test class for SedeDAO
 * Tests all CRUD operations and sede management methods
 */
class SedeDAOTest {

    private SedeDAO sedeDAO;
    private Connection mockConnection;
    private PreparedStatement mockPreparedStatement;
    private ResultSet mockResultSet;
    private MockedStatic<ConPool> mockedConPool;

    @BeforeEach
    void setUp() throws SQLException {
        mockConnection = mock(Connection.class);
        mockPreparedStatement = mock(PreparedStatement.class);
        mockResultSet = mock(ResultSet.class);

        sedeDAO = new SedeDAO();

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

    private Sede createTestSede(int idSede, String citta, String via, int civico, String cap) {
        Sede sede = new Sede();
        sede.setIdSede(idSede);
        sede.setCitta(citta);
        sede.setVia(via);
        sede.setCivico(civico);
        sede.setCap(cap);
        return sede;
    }

    // ==================== doRetrieveById Tests ====================

    @Test
    void testDoRetrieveById_Found() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt(1)).thenReturn(5);
        when(mockResultSet.getString(2)).thenReturn("Milano");
        when(mockResultSet.getString(3)).thenReturn("Via X");
        when(mockResultSet.getInt(4)).thenReturn(12);
        when(mockResultSet.getString(5)).thenReturn("20100");

        SedeDAO spy = spy(sedeDAO);
        doReturn(Collections.emptyList()).when(spy).getPresenza(5);

        // Act
        Sede s = spy.doRetrieveById(5);

        // Assert
        assertNotNull(s);
        assertEquals(5, s.getIdSede());
        assertEquals("Milano", s.getCitta());
        assertEquals("Via X", s.getVia());
        assertEquals(12, s.getCivico());
        assertEquals("20100", s.getCap());
        assertEquals(0, s.getLibri().size());
        verify(mockPreparedStatement).setInt(1, 5);
    }

    @Test
    void testDoRetrieveById_SQLExceptionThrown() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("retrieve error"));

        // Act & Assert
        assertThrows(RuntimeException.class, () -> sedeDAO.doRetrieveById(5));
    }

    // ==================== doRetrivedAll Tests ====================

    @Test
    void testDoRetrivedAll_ReturnsList() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, true, false);
        when(mockResultSet.getInt(1)).thenReturn(1, 2);
        when(mockResultSet.getString(2)).thenReturn("C1", "C2");
        when(mockResultSet.getString(3)).thenReturn("V1", "V2");
        when(mockResultSet.getInt(4)).thenReturn(10, 20);
        when(mockResultSet.getString(5)).thenReturn("10000", "20000");

        SedeDAO spy = spy(sedeDAO);
        doReturn(Collections.emptyList()).when(spy).getPresenza(anyInt());

        // Act
        List<Sede> list = spy.doRetrivedAll();

        // Assert
        assertNotNull(list);
        assertEquals(2, list.size());
        assertEquals(1, list.get(0).getIdSede());
        assertEquals("C1", list.get(0).getCitta());
        assertEquals("V1", list.get(0).getVia());
        assertEquals(10, list.get(0).getCivico());
        assertEquals("10000", list.get(0).getCap());
        assertNotNull(list.get(0).getLibri());
        assertEquals(2, list.get(1).getIdSede());
        assertEquals("C2", list.get(1).getCitta());
        assertEquals("V2", list.get(1).getVia());
        assertEquals(20, list.get(1).getCivico());
        assertEquals("20000", list.get(1).getCap());
        assertNotNull(list.get(1).getLibri());
    }

    @Test
    void testDoRetrivedAll_SQLExceptionThrown() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("retriveAll error"));

        // Act & Assert
        assertThrows(RuntimeException.class, () -> sedeDAO.doRetrivedAll());
    }

    // ==================== doSave Tests ====================

    @Test
    void testDoSave_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString(), anyInt())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);
        when(mockPreparedStatement.getGeneratedKeys()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true);
        when(mockResultSet.getInt(1)).thenReturn(321);

        Sede s = createTestSede(0, "Citta", "Via T", 1, "00000");

        // Act
        sedeDAO.doSave(s);

        // Assert
        assertEquals(321, s.getIdSede());
        verify(mockPreparedStatement).setString(1, "Citta");
        verify(mockPreparedStatement).setString(2, "Via T");
        verify(mockPreparedStatement).setInt(3, 1);
        verify(mockPreparedStatement).setString(4, "00000");
    }

    @Test
    void testDoSave_InsertFails() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("INSERT INTO Sede"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        Sede s = createTestSede(0, "C", "V", 1, "00000");

        // Act & Assert
        assertThrows(RuntimeException.class, () -> sedeDAO.doSave(s));
    }

    @Test
    void testDoSave_NoGeneratedKeys() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString(), anyInt())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);
        when(mockPreparedStatement.getGeneratedKeys()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        Sede s = createTestSede(0, "Citta", "Via T", 1, "00000");

        // Act
        sedeDAO.doSave(s);

        // Assert
        assertEquals(0, s.getIdSede());
    }

    @Test
    void testDoSave_SQLExceptionThrown() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString(), anyInt())).thenThrow(new SQLException("save error"));

        Sede s = createTestSede(0, "Citta", "Via T", 1, "00000");

        // Act & Assert
        assertThrows(RuntimeException.class, () -> sedeDAO.doSave(s));
    }

    @Test
    void testDoSave_GetGeneratedKeysThrowsSQLException() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString(), anyInt())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);
        when(mockPreparedStatement.getGeneratedKeys()).thenThrow(new SQLException("keys error"));

        Sede s = createTestSede(0, "Citta", "Via T", 1, "00000");

        // Act & Assert
        assertThrows(RuntimeException.class, () -> sedeDAO.doSave(s));
    }

    // ==================== updateSede Tests ====================

    @Test
    void testUpdateSede_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("UPDATE Sede SET"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        Sede s = createTestSede(8, "City", "Street", 9, "99999");

        // Act
        assertDoesNotThrow(() -> sedeDAO.updateSede(s));

        // Assert
        verify(mockPreparedStatement).setString(1, "City");
        verify(mockPreparedStatement).setString(2, "Street");
        verify(mockPreparedStatement).setInt(3, 9);
        verify(mockPreparedStatement).setString(4, "99999");
        verify(mockPreparedStatement).setInt(5, 8);
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testUpdateSede_NoRowsUpdated() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("UPDATE Sede SET"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        Sede s = createTestSede(3, "C", "V", 1, "00000");

        // Act & Assert
        assertThrows(RuntimeException.class, () -> sedeDAO.updateSede(s));
    }

    @Test
    void testUpdateSede_SQLExceptionThrown() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("UPDATE Sede SET"))).thenThrow(new SQLException("update error"));

        Sede s = createTestSede(3, "C", "V", 1, "00000");

        // Act & Assert
        assertThrows(RuntimeException.class, () -> sedeDAO.updateSede(s));
    }

    // ==================== deleteSede Tests ====================

    @Test
    void testDeleteSede_WithPresenza_Success() throws SQLException {
        // Arrange
        PreparedStatement ps1 = mock(PreparedStatement.class);
        PreparedStatement ps2 = mock(PreparedStatement.class);

        when(mockConnection.prepareStatement(anyString())).thenReturn(ps1, ps2);
        when(ps1.executeUpdate()).thenReturn(1);
        when(ps2.executeUpdate()).thenReturn(1);

        Sede mockSede = spy(new Sede());
        SedeDAO spyDao = spy(sedeDAO);
        doReturn(Collections.singletonList(new Libro())).when(spyDao).getPresenza(9);
        doReturn(mockSede).when(spyDao).doRetrieveById(anyInt());

        // Act
        assertDoesNotThrow(() -> spyDao.deleteSede(9));

        // Assert
        verify(ps1).setInt(1, 9);
        verify(ps1).executeUpdate();
        verify(ps2).setInt(1, 9);
        verify(ps2).executeUpdate();
        verify(mockSede).setLibri(null);
    }

    @Test
    void testDeleteSede_NoPresenza_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        SedeDAO spyDao = spy(sedeDAO);
        doReturn(Collections.emptyList()).when(spyDao).getPresenza(anyInt());
        doReturn(new Sede()).when(spyDao).doRetrieveById(anyInt());

        // Act
        assertDoesNotThrow(() -> spyDao.deleteSede(21));

        // Assert
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDeleteSede_PresenzaExecuteFails() throws SQLException {
        // Arrange
        PreparedStatement psApp = mock(PreparedStatement.class);
        PreparedStatement psDel = mock(PreparedStatement.class);

        when(mockConnection.prepareStatement(anyString())).thenReturn(psApp, psDel);
        when(psApp.executeUpdate()).thenReturn(0);
        when(psDel.executeUpdate()).thenReturn(1);

        List<Libro> libri = new ArrayList<>();
        libri.add(new Libro());

        SedeDAO spyDao = spy(sedeDAO);
        doReturn(libri).when(spyDao).getPresenza(9);
        doReturn(new Sede()).when(spyDao).doRetrieveById(9);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> spyDao.deleteSede(9));
    }

    @Test
    void testDeleteSede_GetPresenzaNull_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        SedeDAO spyDao = spy(sedeDAO);
        doReturn(null).when(spyDao).getPresenza(anyInt());
        doReturn(new Sede()).when(spyDao).doRetrieveById(anyInt());

        // Act
        assertDoesNotThrow(() -> spyDao.deleteSede(55));

        // Assert
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDeleteSede_FinalDeleteFails() throws SQLException {
        // Arrange
        PreparedStatement psApp = mock(PreparedStatement.class);
        PreparedStatement psDel = mock(PreparedStatement.class);

        when(mockConnection.prepareStatement(anyString())).thenReturn(psApp, psDel);
        when(psApp.executeUpdate()).thenReturn(1);
        when(psDel.executeUpdate()).thenReturn(0);

        List<Libro> libri = new ArrayList<>();
        libri.add(new Libro());

        SedeDAO spyDao = spy(sedeDAO);
        doReturn(libri).when(spyDao).getPresenza(33);
        doReturn(new Sede()).when(spyDao).doRetrieveById(33);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> spyDao.deleteSede(33));
    }

    @Test
    void testDeleteSede_SQLExceptionThrown() throws SQLException {
        // Arrange
        SedeDAO spyDao = spy(sedeDAO);
        doThrow(new RuntimeException(new SQLException("delete error"))).when(spyDao).getPresenza(anyInt());

        // Act & Assert
        assertThrows(RuntimeException.class, () -> spyDao.deleteSede(5));
    }

    // ==================== addLibroSede Tests ====================

    @Test
    void testAddLibroSede_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        Sede sede = new Sede();
        sede.setIdSede(42);
        sede.setLibri(new ArrayList<>());

        Libro l = new Libro();
        l.setIsbn("ABCD");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, ctx) -> when(mock.doRetrieveById("ABCD")).thenReturn(l))) {

            // Act
            sedeDAO.addLibroSede(sede, "ABCD");

            // Assert
            verify(mockPreparedStatement).setInt(1, 42);
            verify(mockPreparedStatement).setString(2, "ABCD");
            verify(mockPreparedStatement).executeUpdate();

            assertEquals(1, sede.getLibri().size());
            assertEquals("ABCD", sede.getLibri().get(0).getIsbn());
        }
    }

    @Test
    void testAddLibroSede_InsertFails() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("INSERT INTO Presenza"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        Sede s = new Sede();
        s.setIdSede(50);
        s.setLibri(new ArrayList<>());

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, ctx) -> when(mock.doRetrieveById("X")).thenReturn(new Libro()))) {

            // Act & Assert
            assertThrows(RuntimeException.class, () -> sedeDAO.addLibroSede(s, "X"));
        }
    }

    @Test
    void testAddLibroSede_SQLExceptionThrown() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("add error"));

        Sede s = new Sede();
        s.setIdSede(50);
        s.setLibri(new ArrayList<>());

        // Act & Assert
        assertThrows(RuntimeException.class, () -> sedeDAO.addLibroSede(s, "X"));
    }

    // ==================== doSavePresenza Tests ====================

    @Test
    void testDoSavePresenza_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        // Act
        assertDoesNotThrow(() -> sedeDAO.doSavePresenza(2, "isbn"));

        // Assert
        verify(mockPreparedStatement).setInt(1, 2);
        verify(mockPreparedStatement).setString(2, "isbn");
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDoSavePresenza_ExecuteUpdateFails() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> sedeDAO.doSavePresenza(2, "isbn"));
    }

    // ==================== deleteFromPresenzaLibro Tests ====================

    @Test
    void testDeleteFromPresenzaLibro_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("DELETE FROM Presenza WHERE"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        // Act
        assertDoesNotThrow(() -> sedeDAO.deleteFromPresenzaLibro(2, "ZISB"));

        // Assert
        verify(mockPreparedStatement).setInt(1, 2);
        verify(mockPreparedStatement).setString(2, "ZISB");
        verify(mockPreparedStatement).executeUpdate();
    }

    @Test
    void testDeleteFromPresenzaLibro_ExecuteUpdateFails() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(0);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> sedeDAO.deleteFromPresenzaLibro(3, "is"));
    }

    @Test
    void testDeleteFromPresenzaLibro_SQLExceptionThrown() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("DELETE FROM Presenza WHERE"))).thenThrow(new SQLException("deleteFrom error"));

        // Act & Assert
        assertThrows(RuntimeException.class, () -> sedeDAO.deleteFromPresenzaLibro(3, "is"));
    }

    // ==================== getPresenza Tests ====================

    @Test
    void testGetPresenza_ReturnsList() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("Presenza"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(true, false);
        when(mockResultSet.getString(1)).thenReturn("ISBX");

        Libro libro = new Libro();
        libro.setIsbn("ISBX");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, ctx) -> when(mock.doRetrieveById("ISBX")).thenReturn(libro))) {

            // Act
            List<Libro> list = sedeDAO.getPresenza(77);

            // Assert
            assertNotNull(list);
            assertEquals(1, list.size());
            assertEquals("ISBX", list.get(0).getIsbn());
            verify(mockPreparedStatement).setInt(1, 77);
        }
    }

    @Test
    void testGetPresenza_EmptyList() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("Presenza"))).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeQuery()).thenReturn(mockResultSet);
        when(mockResultSet.next()).thenReturn(false);

        // Act
        List<Libro> list = sedeDAO.getPresenza(77);

        // Assert
        assertNotNull(list);
        assertEquals(0, list.size());
    }

    @Test
    void testGetPresenza_SQLExceptionThrown() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(contains("Presenza"))).thenThrow(new SQLException("getPresenza error"));

        // Act & Assert
        assertThrows(RuntimeException.class, () -> sedeDAO.getPresenza(77));
    }

    // ==================== removeLibroSede Tests ====================

    @Test
    void testRemoveLibroSede_Success() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenReturn(mockPreparedStatement);
        when(mockPreparedStatement.executeUpdate()).thenReturn(1);

        Sede s = new Sede();
        s.setIdSede(4);
        Libro l = new Libro();
        l.setIsbn("XISBN");
        s.setLibri(new ArrayList<>());
        s.getLibri().add(l);

        SedeDAO spyDao = spy(sedeDAO);
        doReturn(s).when(spyDao).doRetrieveById(4);

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, ctx) -> when(mock.doRetrieveById("XISBN")).thenReturn(l))) {

            // Act
            assertDoesNotThrow(() -> spyDao.removeLibroSede(4, "XISBN"));

            // Assert
            verify(mockPreparedStatement).setInt(1, 4);
            verify(mockPreparedStatement).setString(2, "XISBN");
            verify(mockPreparedStatement).executeUpdate();
        }
    }

    @Test
    void testRemoveLibroSede_SQLExceptionThrown() throws SQLException {
        // Arrange
        when(mockConnection.prepareStatement(anyString())).thenThrow(new SQLException("remove error"));

        Sede s = new Sede();
        s.setIdSede(4);

        SedeDAO spyDao = spy(sedeDAO);
        doReturn(s).when(spyDao).doRetrieveById(4);

        // Act & Assert
        assertThrows(RuntimeException.class, () -> spyDao.removeLibroSede(4, "XISBN"));
    }
}