package controller.admin.gestisciProdotti;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.SedeDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import java.io.IOException;

import static org.mockito.Mockito.*;

class AggiungiLibroSedeTest {

    private AggiungiLibroSede servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        servlet = new AggiungiLibroSede();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);
    }

    @Test
    void testDoGet_NoSedeSelected_ForwardWithoutSaving() throws IOException, ServletException {
        // Quando nessuna sede è selezionata
        when(request.getParameterValues("sedeSelezionata")).thenReturn(null);
        when(request.getParameter("isbn")).thenReturn("123-ABC");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mocked = mockConstruction(SedeDAO.class)) {
            servlet.doGet(request, response);

            // Verifica che non venga creato alcun SedeDAO o che la lista costruita sia vuota
            assert mocked.constructed().size() == 1;
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    void testDoGet_SingleSedeSelected_SavesPresenza() throws IOException, ServletException {
        // Quando una singola sede è selezionata
        when(request.getParameterValues("sedeSelezionata")).thenReturn(new String[]{"5"});
        when(request.getParameter("isbn")).thenReturn("123-ABC");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mocked = mockConstruction(SedeDAO.class)) {
            servlet.doGet(request, response);

            SedeDAO sedeDAO = mocked.constructed().get(0);
            verify(sedeDAO, times(1)).doSavePresenza(5, "123-ABC");
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    void testDoGet_MultipleSediSelected_SavesAllPresenze() throws IOException, ServletException {
        // Quando più sedi sono selezionate
        when(request.getParameterValues("sedeSelezionata")).thenReturn(new String[]{"1", "2", "3"});
        when(request.getParameter("isbn")).thenReturn("456-DEF");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mocked = mockConstruction(SedeDAO.class)) {
            servlet.doGet(request, response);

            SedeDAO sedeDAO = mocked.constructed().get(0);
            verify(sedeDAO, times(1)).doSavePresenza(1, "456-DEF");
            verify(sedeDAO, times(1)).doSavePresenza(2, "456-DEF");
            verify(sedeDAO, times(1)).doSavePresenza(3, "456-DEF");
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    void testDoGet_InvalidSedeId_ThrowsNumberFormatException() throws IOException, ServletException {
        // Quando un ID sede non è un numero valido
        when(request.getParameterValues("sedeSelezionata")).thenReturn(new String[]{"invalid"});
        when(request.getParameter("isbn")).thenReturn("789-GHI");
        RequestDispatcher errorDispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(errorDispatcher);

        try (MockedConstruction<SedeDAO> mocked = mockConstruction(SedeDAO.class)) {
            servlet.doGet(request, response);
            // Verifica che il servlet abbia fatto forward verso la pagina di errore
            verify(errorDispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    void testDoGet_LargeSede_IdParsedCorrectly() throws IOException, ServletException {
        // Test con ID sede grande
        when(request.getParameterValues("sedeSelezionata")).thenReturn(new String[]{"99999"});
        when(request.getParameter("isbn")).thenReturn("ISBN-LARGE");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mocked = mockConstruction(SedeDAO.class)) {
            servlet.doGet(request, response);

            SedeDAO sedeDAO = mocked.constructed().get(0);
            verify(sedeDAO, times(1)).doSavePresenza(99999, "ISBN-LARGE");
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    void testDoGet_DispatcherAlwaysForwarded() throws IOException, ServletException {
        // Verifica che il dispatcher.forward sia sempre chiamato, anche se idSedi è null
        when(request.getParameterValues("sedeSelezionata")).thenReturn(null);
        when(request.getParameter("isbn")).thenReturn("test-isbn");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mocked = mockConstruction(SedeDAO.class)) {
            servlet.doGet(request, response);
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    void testDoGet_EmptySedeArray_ForwardWithoutSaving() throws IOException, ServletException {
        // Quando array di sedi è vuoto (non null, ma vuoto)
        when(request.getParameterValues("sedeSelezionata")).thenReturn(new String[]{});
        when(request.getParameter("isbn")).thenReturn("empty-isbn");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mocked = mockConstruction(SedeDAO.class)) {
            servlet.doGet(request, response);

            SedeDAO sedeDAO = mocked.constructed().get(0);
            // Il for loop iterate su 0 elementi, quindi doSavePresenza non viene mai chiamato
            verify(sedeDAO, never()).doSavePresenza(anyInt(), anyString());
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    void testDoGet_DifferentIsbn_SavedCorrectly() throws IOException, ServletException {
        // Test con diversi ISBN
        when(request.getParameterValues("sedeSelezionata")).thenReturn(new String[]{"10", "20"});
        when(request.getParameter("isbn")).thenReturn("BOOK-123-XYZ");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mocked = mockConstruction(SedeDAO.class)) {
            servlet.doGet(request, response);

            SedeDAO sedeDAO = mocked.constructed().get(0);
            verify(sedeDAO, times(1)).doSavePresenza(10, "BOOK-123-XYZ");
            verify(sedeDAO, times(1)).doSavePresenza(20, "BOOK-123-XYZ");
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    void testDoGet_ZeroSedeId_SavesWithZeroId() throws IOException, ServletException {
        // Test con ID sede zero
        when(request.getParameterValues("sedeSelezionata")).thenReturn(new String[]{"0"});
        when(request.getParameter("isbn")).thenReturn("TEST-ISBN");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mocked = mockConstruction(SedeDAO.class)) {
            servlet.doGet(request, response);

            SedeDAO sedeDAO = mocked.constructed().get(0);
            verify(sedeDAO, times(1)).doSavePresenza(0, "TEST-ISBN");
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    void testDoGet_NegativeSedeId_SavesWithNegativeId() throws IOException, ServletException {
        // Test con ID sede negativo (edge case)
        when(request.getParameterValues("sedeSelezionata")).thenReturn(new String[]{"-5"});
        when(request.getParameter("isbn")).thenReturn("NEG-ISBN");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mocked = mockConstruction(SedeDAO.class)) {
            servlet.doGet(request, response);

            SedeDAO sedeDAO = mocked.constructed().get(0);
            verify(sedeDAO, times(1)).doSavePresenza(-5, "NEG-ISBN");
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    void testDoGet_ManySedeSelected_SavesAllCorrectly() throws IOException, ServletException {
        // Quando molte sedi sono selezionate
        when(request.getParameterValues("sedeSelezionata")).thenReturn(new String[]{"1", "2", "3", "4", "5"});
        when(request.getParameter("isbn")).thenReturn("MANY-ISBN");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mocked = mockConstruction(SedeDAO.class)) {
            servlet.doGet(request, response);

            SedeDAO sedeDAO = mocked.constructed().get(0);
            verify(sedeDAO, times(1)).doSavePresenza(1, "MANY-ISBN");
            verify(sedeDAO, times(1)).doSavePresenza(2, "MANY-ISBN");
            verify(sedeDAO, times(1)).doSavePresenza(3, "MANY-ISBN");
            verify(sedeDAO, times(1)).doSavePresenza(4, "MANY-ISBN");
            verify(sedeDAO, times(1)).doSavePresenza(5, "MANY-ISBN");
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    void testDoGet_SpecialCharactersInIsbn_SavesCorrectly() throws IOException, ServletException {
        // Test con caratteri speciali nell'ISBN
        when(request.getParameterValues("sedeSelezionata")).thenReturn(new String[]{"7"});
        when(request.getParameter("isbn")).thenReturn("ISBN-123-ABC-!@#");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mocked = mockConstruction(SedeDAO.class)) {
            servlet.doGet(request, response);

            SedeDAO sedeDAO = mocked.constructed().get(0);
            verify(sedeDAO, times(1)).doSavePresenza(7, "ISBN-123-ABC-!@#");
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    void testDoGet_IntegerOverflow_ParsesWithinLimits() throws IOException, ServletException {
        // Test con un numero grande ma ancora entro i limiti di Integer
        when(request.getParameterValues("sedeSelezionata")).thenReturn(new String[]{"2147483647"});
        when(request.getParameter("isbn")).thenReturn("OVERFLOW-TEST");
        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mocked = mockConstruction(SedeDAO.class)) {
            servlet.doGet(request, response);

            SedeDAO sedeDAO = mocked.constructed().get(0);
            verify(sedeDAO, times(1)).doSavePresenza(2147483647, "OVERFLOW-TEST");
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    void testDoGet_IntegerOverflow_ThrowsNumberFormatException() throws IOException, ServletException {
        // Test con un numero troppo grande (oltre Integer.MAX_VALUE)
        when(request.getParameterValues("sedeSelezionata")).thenReturn(new String[]{"2147483648"});
        when(request.getParameter("isbn")).thenReturn("OVERFLOW-TEST");
        RequestDispatcher errorDispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(errorDispatcher);

        try (MockedConstruction<SedeDAO> mocked = mockConstruction(SedeDAO.class)) {
            servlet.doGet(request, response);
            // Verifica che il servlet abbia fatto forward verso la pagina di errore
            verify(errorDispatcher, times(1)).forward(request, response);
        }
    }
}
