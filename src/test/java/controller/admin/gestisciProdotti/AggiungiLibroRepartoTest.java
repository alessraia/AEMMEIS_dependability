package controller.admin.gestisciProdotti;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.RepartoDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.Mockito.*;

class AggiungiLibroRepartoTest {

    private AggiungiLibroReparto servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        servlet = new AggiungiLibroReparto();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);
    }

    @Test
    void testDoGet_NoRepartiSelected_ForwardWithoutSaving() throws IOException, ServletException {
        // Quando nessun reparto è selezionato
        when(request.getParameterValues("repartoSelezionato")).thenReturn(null);
        when(request.getParameter("isbn")).thenReturn("123-ABC");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);

        try (MockedConstruction<RepartoDAO> mocked = mockConstruction(RepartoDAO.class)) {
            servlet.doGet(request, response);

            // Verifica che non venga creato alcun RepartoDAO o che la lista costruita sia vuota
            assert mocked.constructed().size() == 1;
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    void testDoGet_SingleRepartoSelected_SavesAppartenenza() throws IOException, ServletException {
        // Quando un singolo reparto è selezionato
        when(request.getParameterValues("repartoSelezionato")).thenReturn(new String[]{"5"});
        when(request.getParameter("isbn")).thenReturn("123-ABC");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);

        try (MockedConstruction<RepartoDAO> mocked = mockConstruction(RepartoDAO.class)) {
            servlet.doGet(request, response);

            RepartoDAO repartoDAO = mocked.constructed().get(0);
            verify(repartoDAO, times(1)).doSaveAppartenenza(5, "123-ABC");
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    void testDoGet_MultipleRepartiSelected_SavesAllAppartenenze() throws IOException, ServletException {
        // Quando più reparti sono selezionati
        when(request.getParameterValues("repartoSelezionato")).thenReturn(new String[]{"1", "2", "3"});
        when(request.getParameter("isbn")).thenReturn("456-DEF");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);

        try (MockedConstruction<RepartoDAO> mocked = mockConstruction(RepartoDAO.class)) {
            servlet.doGet(request, response);

            RepartoDAO repartoDAO = mocked.constructed().get(0);
            verify(repartoDAO, times(1)).doSaveAppartenenza(1, "456-DEF");
            verify(repartoDAO, times(1)).doSaveAppartenenza(2, "456-DEF");
            verify(repartoDAO, times(1)).doSaveAppartenenza(3, "456-DEF");
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    void testDoGet_InvalidRepartoId_ThrowsNumberFormatException() throws IOException, ServletException {
        // Quando un ID reparto non è un numero valido
        when(request.getParameterValues("repartoSelezionato")).thenReturn(new String[]{"invalid"});
        when(request.getParameter("isbn")).thenReturn("789-GHI");

        try (MockedConstruction<RepartoDAO> mocked = mockConstruction(RepartoDAO.class)) {
            assertThrows(NumberFormatException.class, () -> servlet.doGet(request, response));
        }
    }

    @Test
    void testDoGet_LargeReparto_IdParsedCorrectly() throws IOException, ServletException {
        // Test con ID reparto grande
        when(request.getParameterValues("repartoSelezionato")).thenReturn(new String[]{"99999"});
        when(request.getParameter("isbn")).thenReturn("ISBN-LARGE");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);

        try (MockedConstruction<RepartoDAO> mocked = mockConstruction(RepartoDAO.class)) {
            servlet.doGet(request, response);

            RepartoDAO repartoDAO = mocked.constructed().get(0);
            verify(repartoDAO, times(1)).doSaveAppartenenza(99999, "ISBN-LARGE");
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    void testDoGet_DispatcherAlwaysForwarded() throws IOException, ServletException {
        // Verifica che il dispatcher.forward sia sempre chiamato, anche se idReparti è null
        when(request.getParameterValues("repartoSelezionato")).thenReturn(null);
        when(request.getParameter("isbn")).thenReturn("test-isbn");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);

        try (MockedConstruction<RepartoDAO> mocked = mockConstruction(RepartoDAO.class)) {
            servlet.doGet(request, response);
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    void testDoGet_EmptyRepartiArray_ForwardWithoutSaving() throws IOException, ServletException {
        // Quando array di reparti è vuoto (non null, ma vuoto)
        when(request.getParameterValues("repartoSelezionato")).thenReturn(new String[]{});
        when(request.getParameter("isbn")).thenReturn("empty-isbn");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);

        try (MockedConstruction<RepartoDAO> mocked = mockConstruction(RepartoDAO.class)) {
            servlet.doGet(request, response);

            RepartoDAO repartoDAO = mocked.constructed().get(0);
            // Il for loop iterate su 0 elementi, quindi doSaveAppartenenza non viene mai chiamato
            verify(repartoDAO, never()).doSaveAppartenenza(anyInt(), anyString());
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

}
